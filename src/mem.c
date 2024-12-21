#define _DEFAULT_SOURCE

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "mem_internals.h"
#include "mem.h"
#include "util.h"

void debug_block(struct block_header* b, const char* fmt, ... );
void debug(const char* fmt, ... );

extern inline block_size size_from_capacity( block_capacity cap );
extern inline block_capacity capacity_from_size( block_size sz );

static bool            block_is_big_enough( size_t query, struct block_header* block ) { return block->capacity.bytes >= query; }
static size_t          pages_count   ( size_t mem )                      { return mem / getpagesize() + ((mem % getpagesize()) > 0); }
static size_t          round_pages   ( size_t mem )                      { return getpagesize() * pages_count( mem ) ; }

static void block_init( void* restrict addr, block_size block_sz, void* restrict next ) {
  *((struct block_header*)addr) = (struct block_header) {
    .next = next,
    .capacity = capacity_from_size(block_sz),
    .is_free = true
  };
}

static size_t region_actual_size( size_t query ) { return size_max( round_pages( query ), REGION_MIN_SIZE ); }

extern inline bool region_is_invalid( const struct region* r );



static void* map_pages(void const* addr, size_t length, int additional_flags) {
  return mmap( (void*) addr, length, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | additional_flags , -1, 0 );
}

/*  аллоцировать регион памяти и инициализировать его блоком */
static struct region alloc_region  ( void const * addr, size_t query ) {
    int extends = 1;
    size_t actual_region_queried_size = region_actual_size(size_from_capacity((block_capacity){query}).bytes);
    void* region_addr = map_pages(addr, actual_region_queried_size,MAP_FIXED_NOREPLACE);
    if(region_addr == MAP_FAILED) {
        region_addr = map_pages(addr, actual_region_queried_size,0);
        extends = 0;
    }
    if(region_addr == MAP_FAILED) return REGION_INVALID;
    struct region region =
    {
        .addr = region_addr,
        .size = actual_region_queried_size,
        .extends = extends
    };
    block_init(region_addr, (block_size){actual_region_queried_size}, NULL);
    return region;
}

static void* block_after( struct block_header const* block )         ;

void* heap_init( size_t initial ) {
  const struct region region = alloc_region( HEAP_START, initial );
  if ( region_is_invalid(&region) ) return NULL;

  return region.addr;
}

#define BLOCK_MIN_CAPACITY 24

/*  --- Разделение блоков (если найденный свободный блок слишком большой )--- */

static bool block_splittable( struct block_header* restrict block, size_t query) {
  return block-> is_free && query + offsetof( struct block_header, contents ) + BLOCK_MIN_CAPACITY <= block->capacity.bytes;
}

static bool split_if_too_big( struct block_header* block, size_t query ) {
  if(!block_splittable(block,query))return false;
  block_capacity left = (block_capacity) {block->capacity.bytes-query-size_from_capacity((block_capacity){0}).bytes};
  if(left.bytes < BLOCK_MIN_CAPACITY) return false;
  struct block_header* new_block = (struct block_header*)(block->contents+query);
  block_init(new_block,size_from_capacity(left),block->next);
  block->next = new_block;
  block->capacity.bytes = query;
  return true;
}


/*  --- Слияние соседних свободных блоков --- */

static void* block_after( struct block_header const* block ) {
  return  (void*) (block->contents + block->capacity.bytes);
}
static bool blocks_continuous (
                               struct block_header const* fst,
                               struct block_header const* snd ) {
  return (void*)snd == block_after(fst);
}
/*  освободить всю память, выделенную под кучу */
#define MUNMAP_ERR -1
void heap_term() {
  struct block_header* cur_block = (struct block_header*)HEAP_START;
  block_size cur_size = (block_size){0};
  struct block_header* cur_region = (struct block_header*) HEAP_START;
  while (cur_block) {
    cur_size.bytes += size_from_capacity(cur_block->capacity).bytes;
    if (!blocks_continuous(cur_block, cur_block->next)) {
      struct block_header* next = cur_block->next;
      if(munmap(cur_region, cur_size.bytes)==MUNMAP_ERR) exit(ERRCODE_MUNMAP_FAILED);
      cur_region = next;
      cur_size.bytes = 0;
      cur_block = next;
    }
    else cur_block = cur_block->next;
  }
}

static bool mergeable(struct block_header const* restrict fst, struct block_header const* restrict snd) {
  return fst->is_free && snd->is_free && blocks_continuous( fst, snd ) ;
}

static bool try_merge_with_next( struct block_header* block ) {
  if(block==NULL)return false;
  struct block_header* next_block = block->next;
  if(next_block == NULL || !mergeable(block,next_block))return false;
  block->next = next_block->next;
  block->capacity.bytes += size_from_capacity(next_block->capacity).bytes;
  return true;
}


/*  --- ... ecли размера кучи хватает --- */

struct block_search_result {
  enum {BSR_FOUND_GOOD_BLOCK, BSR_REACHED_END_NOT_FOUND, BSR_CORRUPTED} type;
  struct block_header* block;
};


static struct block_search_result find_good_or_last  ( struct block_header* restrict block, size_t sz )    {
  if(block == NULL)return (struct block_search_result){BSR_CORRUPTED, block};
  while(true){
    if(block->is_free){
        while(try_merge_with_next(block));
        if(block->capacity.bytes >= sz)return (struct block_search_result) {BSR_FOUND_GOOD_BLOCK, block};
    }
    if(block->next == NULL)break;
    block = block->next;
  }
  return (struct block_search_result){BSR_REACHED_END_NOT_FOUND, block};
}

/*  Попробовать выделить память в куче начиная с блока `block` не пытаясь расширить кучу
 Можно переиспользовать как только кучу расширили. */
static struct block_search_result try_memalloc_existing ( size_t query, struct block_header* block ) {
     struct block_search_result res = find_good_or_last(block,query);
     if(res.type == BSR_FOUND_GOOD_BLOCK){
        split_if_too_big(res.block, query);
        res.block->is_free = false;
     }
     return res;
}



static struct block_header* grow_heap( struct block_header* restrict last, size_t query ) {
  if(last == NULL) return NULL;
  struct region region = alloc_region(block_after(last),query);
  if(region_is_invalid(&region))return NULL;
  last->next = region.addr;
  if(region.extends && try_merge_with_next(last))return last;
  return region.addr;
}

/*  Реализует основную логику malloc и возвращает заголовок выделенного блока */
static struct block_header* memalloc( size_t query, struct block_header* heap_start) {
    query = query > BLOCK_MIN_CAPACITY ? query : BLOCK_MIN_CAPACITY;
    struct block_search_result res = try_memalloc_existing(query, heap_start);
    if(res.type == BSR_REACHED_END_NOT_FOUND){
        heap_start = grow_heap(res.block, query);
        if(heap_start == NULL)return NULL;
        res = try_memalloc_existing(query,heap_start);
        if(res.type != BSR_FOUND_GOOD_BLOCK)return NULL;
        return res.block;
    }
    else if(res.type == BSR_CORRUPTED)return NULL;
    return res.block;
}

void* _malloc( size_t query ) {
  struct block_header* const addr = memalloc( query, (struct block_header*) HEAP_START );
  if (addr) return addr->contents;
  else return NULL;
}

static struct block_header* block_get_header(void* contents) {
  return (struct block_header*) (((uint8_t*)contents)-offsetof(struct block_header, contents));
}

void _free( void* mem ) {
  if (!mem) return ;
  struct block_header* header = block_get_header( mem );
  header->is_free = true;
  while(try_merge_with_next(header));
}
