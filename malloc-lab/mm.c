/*
 * mm.c - A dynamic memory allocator using a Segregated Explicit Free List.
 *
 * All free blocks are organized into N_LISTS segregated doubly linked lists
 * based on block size. LIFO policy is used for insertion within each list.
 *
 * NOTE: 64-bit environment compatible (WSIZE=8, DSIZE=16, 16-byte alignment).
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 64-bit system compatibility: WSIZE=8, DSIZE=16, 16-byte alignment */
#define WSIZE 8             /* Word and header/footer size (bytes) */
#define DSIZE 16            /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */
#define ALIGNMENT 16        /* 16-byte alignment */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0xF)

#define MAX(x, y) ((x) > (y) ? x : y)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word (size_t = 8 bytes) at address p */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0xF)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Segregated List specific macros and variables */
/* Pointers are 8 bytes (WSIZE) each */
#define PREV_FREE_BLKP(bp) ((char *)(bp))         // Address of PRED pointer
#define NEXT_FREE_BLKP(bp) ((char *)(bp) + WSIZE) // Address of SUCC pointer

#define GET_PRED(bp) (*(char **)(PREV_FREE_BLKP(bp)))
#define GET_SUCC(bp) (*(char **)(NEXT_FREE_BLKP(bp)))
#define SET_PRED(bp, pred) (*(char **)(PREV_FREE_BLKP(bp)) = (pred))
#define SET_SUCC(bp, succ) (*(char **)(NEXT_FREE_BLKP(bp)) = (succ))

#define N_LISTS 10              /* Number of segregation lists */
static char *heap_listp;        /* Pointer to the first block */
static void *seg_list[N_LISTS]; /* Array of segregated list heads */

/* Function prototypes for private helper functions */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static int get_list_index(size_t size);
static void insert_block(void *bp);
static void remove_block(void *bp);

/*
 * get_list_index - Determine which list to use based on size
 */
static int get_list_index(size_t size)
{
    if (size <= 16)
        return 0;
    if (size <= 32)
        return 1;
    if (size <= 64)
        return 2;
    if (size <= 128)
        return 3;
    if (size <= 256)
        return 4;
    if (size <= 512)
        return 5;
    if (size <= 1024)
        return 6;
    if (size <= 2048)
        return 7;
    if (size <= 4096)
        return 8;
    return 9; // Largest bin for all remaining sizes
}

/*
 * insert_block - Insert a block into the explicit free list (LIFO)
 */

static void insert_block(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);
    char *curr = seg_list[index];
    char *prev = NULL;

    // Traverse to find the correct position (size-ascending)
    while (curr != NULL && GET_SIZE(HDRP(curr)) < size)
    {
        prev = curr;
        curr = GET_SUCC(curr);
    }

    SET_SUCC(bp, curr);
    SET_PRED(bp, prev);

    if (curr != NULL)
        SET_PRED(curr, bp);

    if (prev != NULL)
        SET_SUCC(prev, bp);
    else
        seg_list[index] = bp; // bp becomes head if prev is NULL
}

/*
 * remove_block - Remove a block from its specific explicit free list
 */

static void remove_block(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);
    char *pred = GET_PRED(bp);
    char *succ = GET_SUCC(bp);

    if (pred == NULL)
        seg_list[index] = succ;
    else
        SET_SUCC(pred, succ);

    if (succ != NULL)
        SET_PRED(succ, pred);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    int prev_free = !prev_alloc;
    int next_free = !next_alloc;

    if (!prev_alloc)
        remove_block(PREV_BLKP(bp));
    if (!next_alloc)
        remove_block(NEXT_BLKP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1: no coalesce */
    }
    else if (prev_alloc && next_free)
    { /* Case 2: next free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { /* Case 3: prev free */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    { /* Case 4: both free */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // Insert **once** after coalesce
    insert_block(bp);
    return bp;
}
/*
 * extend_heap - Extends the heap with a new free block and coalesces.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free (and insert into list) */
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int i;
    /* Initialize all segregated list heads to NULL */
    for (i = 0; i < N_LISTS; i++)
    {
        seg_list[i] = NULL;
    }

    /* Create the initial empty heap (4 * WSIZE = 32 bytes) */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding (8 bytes) */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);                     /* heap_listp points to the payload of the prologue block */

    /* Extend the heap with a CHUNKSIZE bytes free block */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * place - Place block of asize bytes at start of free block bp
 * and split if remainder is at least minimum block size (2*DSIZE=32).
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

    size_t min_block = 2 * DSIZE;
    if (csize - asize >= min_block)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_block(next_bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * find_fit - Find a fit for a block with asize bytes (First-Fit on SegList)
 */
static void *find_fit(size_t asize)
{
    int index = get_list_index(asize);
    char *bp;
    char *best_bp = NULL;
    size_t min_diff = (size_t)-1;

    // Search each list starting from index
    for (; index < N_LISTS; index++)
    {
        for (bp = seg_list[index]; bp != NULL; bp = GET_SUCC(bp))
        {
            size_t bsize = GET_SIZE(HDRP(bp));
            if (bsize >= asize)
            {
                size_t diff = bsize - asize;
                if (diff < min_diff)
                {
                    best_bp = bp;
                    min_diff = diff;
                    if (diff == 0)
                        return best_bp; // perfect fit
                }
            }
        }
        if (best_bp != NULL)
            return best_bp;
    }

    return NULL; // no fit
}
/*
 * mm_malloc - Allocate a block by searching the free list.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    // Minimum block size for explicit list is 2*DSIZE (32 bytes)
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        // asize = ALIGN(payload size + overhead size)
        asize = ALIGN(size + DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Extend heap and place the block */
    // extendsize = ((asize + CHUNKSIZE - 1) / CHUNKSIZE) * CHUNKSIZE;
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block and coalescing it.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    // Mark block as free
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // Coalesce with neighbors and insert the new free block into the free list
    coalesce(bp);
}

/*
 * mm_realloc - Simple realloc implementation using mm_malloc and mm_free.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // Get the actual payload size of the old block (Total size - Overhead DSIZE)
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;

    if (size < copySize)
        copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}
