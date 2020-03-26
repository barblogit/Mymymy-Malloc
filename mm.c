/*
 * Summary: This implementation of malloc and related functions uses the
 * Segregated Fits strategy introduced on pp864-865 of CSAPP.
 *
 * More specifically, we maintain an array of pointers to free lists of
 * different sizes. This array is not stored as a global variable, but rather
 * at the beginning of the heap, right before the prologue. Each free list is
 * and explicit list, with each block having a predecessor pointer and successor
 * pointer next to the block header.
 *
 * Allocated blocks do not store such pointers and therefore the entire heap can
 * be traversed like an implicit list.
 *
 * The placement policy is a variant of First Fit, in that the first block in a
 * suitable free list is popped and allocated for a new payload. However, when
 * we insert a new free block into a free list, we make sure to maintain an
 * ascending order in terms of block size. As a result, this placement policy is
 * also similar to Best Fit.
 *
 * Coalescing is performed everytime the heap is extended or a block is freed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "barblog",
    /* First member's full name */
    "",
    /* First member's email address */
    "",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* uncomment the following line when debugging using mm_check */
//#define DEBUG      TRUE
/* uncomment the following line when debugging in verbose mode */
//#define VERBOSE    TRUE

/* Basic macros, reference: CSAPP 9.9 p857 */
#define ALIGNMENT  __SIZEOF_POINTER__
#define ALIGN(size) ((((size) + (ALIGNMENT-1)) / (ALIGNMENT)) * (ALIGNMENT))

#define WSIZE      __SIZEOF_POINTER__       // word, size of header/footer
#define DSIZE      2*WSIZE                  // double word
#define CHUNKSIZE ((1<<12) + DSIZE)  // extend heap by how many bytes
#define INITSIZE  ((1<<7) + DSIZE)   // initialize how many bytes
#define LISTSIZE   16      // how many free lists we want
#define THRESHOLD  7       // threshold tuned for placement policy

#define MAX(x, y) ((x) > (y)? (x) : (y))

// pack size and allocation bit into header/footer
#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(unsigned long *)(p))
#define PUT(p, val) (*(unsigned long *)(p) = (unsigned long)(val))

// read the size and allocated bit from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// our free blocks have two words following the header,
// one for predecessor pointer and one for successor pointer
#define PRED_BLKP(bp) (*(char **)(bp))              // address of predecessor blk
#define SUCC_BLKP(bp) (*(char **)((char *)(bp) + WSIZE)) // addr of successor blk


/* Global variable */
static char * heap_ptr; // points to the prologue block of the heap


// we store pointers to free lists before the prologue block
// we can quickly get the address of any of the pointers
static inline char * freelists(int index) {
    return heap_ptr - (LISTSIZE + 1 - index) * WSIZE;
}

/* Helper function declarations */
static void * extend_heap(size_t size);
static void * coalesce(void * ptr);
static void * place(void * ptr, size_t size);
static void add_free(void * ptr, size_t size); // add free block to a free list
static void pop_free(void * ptr);              // delete free block from a list
static size_t align_size(size_t size);
#ifdef DEBUG
static int mm_check();                         // heap consistency checker
#endif


/*
 * Initilize the heap, including the free list pointers
 */
int mm_init(void)
{
    // create initial empty heap
#ifdef DEBUG
    mem_init();
#endif
    if ((heap_ptr = mem_sbrk((LISTSIZE + 4) * WSIZE)) == (void *) -1)
        return -1;

    // alignment padding is not needed when WSIZE % 8, but makes code compatible
    // with WSIZE % 4 but ALIGNMENT % 8 (e.g. 32 bit version, doubleword-aligned)
    PUT(heap_ptr, 0);
    PUT(heap_ptr + ((LISTSIZE + 1)*WSIZE), PACK(DSIZE, 1));  // prologue header
    PUT(heap_ptr + ((LISTSIZE + 2)*WSIZE), PACK(DSIZE, 1));  // prologue footer
    PUT(heap_ptr + ((LISTSIZE + 3)*WSIZE), PACK(0, 1));      // epilogue header

    for (int i = 1; i < LISTSIZE + 1; ++i) {
        PUT(heap_ptr + (i*WSIZE), 0);                        // free list pointers
    }
    heap_ptr += (LISTSIZE + 2) * WSIZE;

    // extend heap with a free block of CHUNKSIZE bytes
    if (extend_heap(INITSIZE) == NULL)
        return -1;

#ifdef VERBOSE
    printf("\n\n************* Heap initialized *************\n\n");
#endif
#ifdef DEBUG
    if (mm_check() == 0)
        return -1;
#endif

    return 0;
}

/*
 * Allocate memory for payload of size bytes
 */
void * mm_malloc(size_t size)
{
    if (size == 0) return NULL;

    // since we include predecessor and successor pointers in a free block
    // minimum block size is 4 words
    size = align_size(size);

    // look for a fitting size from free lists
    // and since we order within each free list from small to larger size blocks,
    // we just need to check the block pointed from the free list pointer
    // which is at the beginning of the heap (before the prologue)
    int index = 0;
    void * bp = NULL;
    while (index < LISTSIZE) {
        if (GET(freelists(index)) != 0 &&
            GET_SIZE(HDRP(*(char**)freelists(index))) > size) {
            bp = *(char **)freelists(index);
            break;
        }
        ++index;
    }

    // if no free block is found
    if (!bp) {
        if ((bp = extend_heap(MAX(size, CHUNKSIZE))) == NULL)
            return NULL;
    }
    // allocate new block in the free block we found or extended
    bp = place(bp, size);

#ifdef VERBOSE
    printf("Malloc'd for %lu bytes...\n", size);
#endif
#ifdef DEBUG
    mm_check();
#endif

    return bp;
}

/*
 * Free memory block, update free list, and coalesce
 */
void mm_free(void * bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    add_free(bp, size);
    coalesce(bp);

#ifdef VERBOSE
    printf("Freed %lu bytes at %p...\n", size, bp);
#endif
#ifdef DEBUG
    mm_check();
#endif

}

/*
 * Reallocate memory for payload of size bytes, given a block
 */
void * mm_realloc(void * bp, size_t size)
{
    if (size == 0) return NULL;
    size = align_size(size);

    // case 0: return bp directly if size is less than size of bp
    if (GET_SIZE(HDRP(bp)) >= size)
        return bp;

    int rem_size;
    int next_epi  = !GET_SIZE(HDRP(NEXT_BLKP(bp)));
    int next_free = !GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    void * new_bp = bp;

    // case 1: next blocks are usable
    if (next_free || next_epi) {
        rem_size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - size;
        // case 1-a: next blocks usable, but not enough
        if (rem_size < 0) {
            if (extend_heap(MAX(CHUNKSIZE, -rem_size)) == NULL)
                return NULL;
            rem_size += MAX(CHUNKSIZE, -rem_size);
        }
        // case 1-b: next block usable, and sufficed or now suffices
        pop_free(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size + rem_size, 1));
        PUT(FTRP(bp), PACK(size + rem_size, 1));
    }

    // case 2: next blocks are not usable, call mm_maloc and free old block
    else {
        new_bp = mm_malloc(size);
        memcpy(new_bp, bp, GET_SIZE(HDRP(bp)));
        mm_free(bp);
    }

#ifdef VERBOSE
    printf("Realloc'd block at %p to %lu bytes...\n", bp, size);
#endif
#ifdef DEBUG
    mm_check();
#endif
    return new_bp;
}




/********************************
 * Helper functions
 ********************************/

// helper function: given a size, return an aligned size
static size_t align_size(size_t size)
{
    if (size <= DSIZE) {
        size = 2 * DSIZE;
    } else {
        size = ALIGN(size + DSIZE);
    }
    return size;
}

/*
 * Return a pointer to the header of a new chunk
 */
static void * extend_heap(size_t size)
{
#ifdef VERBOSE
    printf("Extending heap by %lu bytes...\n", size);
#endif

    char * bp;
    size = ALIGN(size);

    // bp points to the first word of the chunk next to old epilogue
    // consequently, old epilogue becomes the header of the new chunk
    if ((bp = mem_sbrk(size)) == (char *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));          // set header of new free block
    PUT(FTRP(bp), PACK(size, 0));          // set footer of new free block
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // set new epilogue header

    add_free(bp, size); // update free lists

    // combine the new free block with any contiguous preceding free blocks
    return coalesce(bp);
}


/*
 * Coalesce with previous and/or next blocks
 */
static void * coalesce(void * bp)
{
    int prev_free = (!GET_ALLOC(HDRP(PREV_BLKP(bp))));
    int next_free = !GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    int size      = GET_SIZE(HDRP(bp));

    // no neighboring free blocks
    if (!prev_free && !next_free)
        return bp;

    pop_free(bp);

    // coalesce with previous block if it is free
    if (prev_free) {
        pop_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // coalesce with next block if it is free
    if (next_free) {
        pop_free(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(bp), PACK(size, 0));
    }

    add_free(bp, size);
    return bp;
}


// helper function: front-load or back-load a payload in a free block
static void inline place_fb (void * bp, size_t fsize, size_t bsize, int alloc)
{
    PUT(HDRP(bp), PACK(fsize, alloc));
    PUT(FTRP(bp), PACK(fsize, alloc));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(bsize, !alloc));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(bsize, !alloc));
}

/*
 * To malloc, place the payload of size size into the block bp we just found
 */
static void * place(void * bp, size_t size)
{
    size_t total_size = GET_SIZE(HDRP(bp));
    size_t rem_size = total_size - size;
    pop_free(bp);

    // case 1: remaining space is less than the minimal size (4 words)
    if (rem_size < 4 * WSIZE) {
        PUT(HDRP(bp), PACK(total_size, 1));
        PUT(FTRP(bp), PACK(total_size, 1));
    }

    // for case 2 and 3, we essentially want to decide whether to allocate the
    // first portion of the free block for the payload or the latter portion
    // the threshold is based on the experiments
    // case 2: remaining space sufficient, and the remaining size relatively big
    else if (rem_size >= THRESHOLD * size) {
        place_fb(bp, size, rem_size, 1);
        add_free(NEXT_BLKP(bp), rem_size); // add remaining free block to free list
    }

    // case 3: remaining space sufficient, and the remaining size relatively small
    else {
        place_fb(bp, rem_size, size, 0);
        add_free(bp, rem_size);
        return NEXT_BLKP(bp);
    }

    return bp;
}


// helper function: given a size, return an index in the free list
// the i-th free list stores blocks of up to 4*WSIZE ^ (i+1) bytes
// the index returned is such that the index-th free list can store
// a block of size bytes
static int index_of(size_t size)
{
    int index = 0;
    for (int curr_size = 4*WSIZE; curr_size < ((4*WSIZE)<<(LISTSIZE-1)); curr_size*=2)
    {
        if (curr_size >= size)
            break;
        ++index;
    }
    return index;
}


/*
 * Add a free block of size size to one of the free lists
 */
static void add_free(void * bp, size_t size)
{
    // find the corresponding free list for the size
    int index = index_of(size);

    // in the free list, find the corresponding block (first fit)
    //    case 1: free list is empty
    char * curr_ptr = !GET(freelists(index))? NULL : *(char **)freelists(index);
    char * pred_ptr = curr_ptr;
    //    case 2: free list is not empty
    while ((curr_ptr != NULL) && size > GET_SIZE(HDRP(curr_ptr))) {
        pred_ptr = curr_ptr;
        curr_ptr = SUCC_BLKP(curr_ptr);
    }

    // by the info we got so far, we know where to place the new free block
    //  possibility 1: free list is empty
    if (GET(freelists(index)) == 0) {
        PUT(bp, NULL);
        PUT((char *)bp + WSIZE, NULL);
        PUT(freelists(index), bp);
    }

    //  possibility 2: free list is not empty, but ptr is NULL, meaning --
    //                 we are adding the free block at the end of the free list
    else if (curr_ptr == NULL) {
        PUT(bp, pred_ptr);
        PUT((char *)bp + WSIZE, NULL);
        PUT((char *)pred_ptr + WSIZE, bp);
    }

    //  possibility 3: free list is not empty, ptr is the first block in free list
    else if (curr_ptr == *(char **)freelists(index)) {
        PUT(bp, NULL);
        PUT((char *)bp + WSIZE, curr_ptr);
        PUT(curr_ptr, bp);
        PUT(freelists(index), bp);
    }

    //  possibility 4: free list is not empty, ptr is in the middle of free list
    else {
        PUT(bp, pred_ptr);
        PUT((char *)bp + WSIZE, curr_ptr);
        PUT(curr_ptr, bp);
        PUT((char *)pred_ptr + WSIZE, bp);
    }
}


/*
 * Delete a block from a free list because it has just been allocated
 */
static void pop_free(void * bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = index_of(size);

    if (PRED_BLKP(bp) == NULL) {

        //  possibility 1: predecessor is null, successor is null
        if (SUCC_BLKP(bp) == NULL) {
            PUT(freelists(index), 0);
        }
        //  possibility 2: predecessor is null, successor is not null
        else {
            PUT(freelists(index), SUCC_BLKP(bp));
            PUT(SUCC_BLKP(bp), NULL);
        }
    }

    else {

        //  possibility 3: predecessor is not null, successor is null
        if (SUCC_BLKP(bp) == NULL) {
            PUT((char *)PRED_BLKP(bp) + WSIZE, NULL);
        }
        //  possibility 4: predecessor is not null, successor is not null
        else {
            PUT((char *)PRED_BLKP(bp) + WSIZE, SUCC_BLKP(bp));
            PUT((char *)SUCC_BLKP(bp), PRED_BLKP(bp));
        }
    }
}



#ifdef DEBUG
/**********************************
 * Heap consistency checker
 **********************************/

// prints contents of block: "addr: header: size,alloc || footer: size,alloc"
static void printblock(void *bp)
{
#ifdef VERBOSE
    unsigned long hdr_size, hdr_alloc, ftr_size, ftr_alloc;

    hdr_size  = GET_SIZE(HDRP(bp));
    hdr_alloc = GET_ALLOC(HDRP(bp));
    ftr_size  = GET_SIZE(FTRP(bp));
    ftr_alloc = GET_ALLOC(FTRP(bp));

    if (hdr_size == 0) {
        printf("%p: epilogue\n", bp);
        return;
    }

    printf("%p: header: %lu,%lu || footer: %lu,%lu\n",
            bp, hdr_size, hdr_alloc, ftr_size, ftr_alloc);
#endif
}

/*
 * checks 1. prologue and epilogue are good
 *        2. every block in free list marked as free
 *        3. every free block is in free list
 *        4. no contiguous free blocks
 *        5. payloads do not overlap
 *        6. heapsize = free block size + alloc block size + auxiliary data
 */
static int mm_check()
{
#ifdef VERBOSE
    printf("*** Heap Checker ***\n\nheap at (%p):\n\n", heap_ptr);

    // print free list pointers
    printf("Free list pointers: \n");
    for (int i = 0; i < LISTSIZE; ++i) {
        if (i < 9) printf(" ");
        printf("%i. %lx", i+1, GET(freelists(i)));
        if (GET(freelists(i)) == 0) printf("           ");
        printf(" | ");
        if ((i+1) % 4 == 0) printf("\n");
    }
    printf("\n");
#endif
    // check prologue and epilogue
    if ((GET_SIZE(HDRP(heap_ptr)) != DSIZE) || !GET_ALLOC(HDRP(heap_ptr))) {
        printf("Bad prologue header\n");
        printf("%lu\n", GET_SIZE(HDRP(heap_ptr)));
        return 0;
    }
    if ((GET_SIZE(mem_heap_hi() - WSIZE + 1) != 0) ||
                    !GET_ALLOC(mem_heap_hi() - WSIZE + 1)) {
        printf("Bad epilogue header\n");
        return 0;
    }

    // check if every block in the free list marked as free, and keep count
    // also keep count of total free block size, version 1
    char * bp;
    int count = 0;
    size_t fre_size_explicit = 0;
    for (int i = 0; i < LISTSIZE; ++i) {
        if (GET(freelists(i)) != 0) {
            ++count;
            bp = *(char **)freelists(i);
            fre_size_explicit += GET_SIZE(HDRP(bp));
            if (GET_ALLOC(HDRP(bp)) == 1) {
                printf("Block %p in free list not marked as free\n", bp);
                return 0;
            }
            while ((bp = SUCC_BLKP(bp)) != NULL) {
                ++count;
                fre_size_explicit += GET_SIZE(HDRP(bp));
                if (GET_ALLOC(HDRP(bp)) == 1) {
                    printf("Block %p in free list not marked as free\n", bp);
                    return 0;
                }
            }
        }
    }
#ifdef VERBOSE
    printf("Free blocks in free lists: %i\n", count);
#endif
    // check if there are contiguous free blocks, and keep count
    // also keep count of the total payload size
    // also keep count of total free block size, version 2
    bp = heap_ptr;
    int consec = 0;
    size_t pld_size = 0;
    size_t fre_size_implicit = 0;
    while ((unsigned long)bp < (unsigned long)mem_heap_hi()) {
        if (GET_ALLOC(HDRP(bp)) == 0) {
            --count;
            ++consec;
            fre_size_implicit += GET_SIZE(HDRP(bp));
        } else {
            pld_size += GET_SIZE(HDRP(bp));
        }

        if (consec >= 2) {
            printf("Contiguous free blocks at %p\n", bp);
            return 0;
        }
        --consec;
        printblock(bp); // print contents of each block
        bp = NEXT_BLKP(bp);
    }

    // check if all free blocks are in free list and vice versa
    if (count < 0) {
        printf("Free block not captured in free lists\n");
        return 0;
    }
    if (count > 0) {
        printf("Free block duplicate in free lists\n");
        return 0;
    }

    // check if explicit free block size equals implicit free block size
    if (fre_size_explicit != fre_size_implicit) {
        printf("Total free block size (explicit vs implicit) inconsistent\n");
        return 0;
    }

    // check if there is potential payload overlap
    // freeblk size + payld size + (freelist ptrs + epilog hdr + heap initial padding)
    // should be equal to total heapsize
    if (fre_size_explicit + pld_size + ((LISTSIZE+2) * WSIZE)> mem_heapsize()) {
        printf("Potential payload overlap\n");
        return 0;
    }
    return 1;
}
#endif
