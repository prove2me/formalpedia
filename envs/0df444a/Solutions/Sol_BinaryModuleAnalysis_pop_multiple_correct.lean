-- Prove2me | solution 1 for BinaryModuleAnalysis.pop_multiple_correct
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:51.420981+00:00
-- url     : https://prove2.me/submissions/d41a82ed-4764-4723-8048-4b5d4cb22f2b

import Definitions.Def_Algo_indexed_heap_Analysis
import Theorems.Thm_BinaryModuleAnalysis_sift_down_loop


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_rep`: Empty heap representation.
- `insert_correct`: Insertion correctness and cost.
- `decrease_correct`: Decrease-key correctness and cost.
- `pop_correct`: Minimum extraction correctness and cost.
-/

open Algo.indexed_heap Algo.indexed_heap.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated

namespace BinaryModuleAnalysis

-- A small source-facing description of the object's storage. The three arrays
-- are separate mutable sequences; aliases to the MinHeap object remain valid.




-- These observations use only the generated field interface. Updating an
-- array does not replace the object's fields or change its identity.




-- Exact heap effect of swap, including the cost counter. The original two
-- vertices are read before either array is changed, including when i = j.


theorem swap_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    MinHeap.swap.Call heap (queue, i, j) (swapHeap heap layout i j) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_swap_pc9 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc8 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc7 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc6 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc5 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc4 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_swap_pc3 _ _ _)
  apply Reaches.prepend (Step.MinHeap_swap_pc2 _ _ _)
  simp only [vertices_write, positions_write, valid.readVertices, valid.readPositions,
    Option.getD_some, swapHeap]
  exact Reaches.single (Step.MinHeap_swap_pc1 _ _ _)

-- A permutation of positions, with all other positions left fixed.


theorem swap_vertices (heap : Heap) (layout : Layout) (i j index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.vertices index =
      exchange (heap.read layout.vertices) i j index := by
  simp [swapHeap, exchange, Heap.read, Heap.write, separate]

theorem swap_positions (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (swapHeap heap layout i j).read layout.positions vertex =
      if vertex = heap.read layout.vertices j then i
      else if vertex = heap.read layout.vertices i then j
      else heap.read layout.positions vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separate]





-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.


theorem Indexed.distinct {vertices positions : Seq} {size i j : Int}
    (indexed : Indexed vertices positions size)
    (iNonnegative : 0 ≤ i) (iBound : i < size)
    (jNonnegative : 0 ≤ j) (jBound : j < size) :
    vertices i = vertices j → i = j := by
  intro same
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  rw [same] at left
  exact left.symm.trans right





-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.
theorem swap_preserves_indexed (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) :
    Indexed ((swapHeap heap layout i j).read layout.vertices)
      ((swapHeap heap layout i j).read layout.positions) layout.size := by
  have left := indexed.forward i iNonnegative iBound
  have right := indexed.forward j jNonnegative jBound
  have equalIndices : heap.read layout.vertices i = heap.read layout.vertices j → i = j :=
    indexed.distinct iNonnegative iBound jNonnegative jBound
  constructor
  · intro index nonnegative bound
    rw [swap_vertices heap layout i j index separate]
    by_cases atRight : index = j
    · subst index
      rw [exchange_right, swap_positions heap layout i j _ separate]
      by_cases same : heap.read layout.vertices i = heap.read layout.vertices j
      · simp [equalIndices same]
      · simp [same]
    · by_cases atLeft : index = i
      · subst index
        rw [exchange_left, swap_positions heap layout i j _ separate]
        simp
      · have notRight : heap.read layout.vertices index ≠ heap.read layout.vertices j := by
          intro same
          exact atRight (indexed.distinct nonnegative bound jNonnegative jBound same)
        have notLeft : heap.read layout.vertices index ≠ heap.read layout.vertices i := by
          intro same
          exact atLeft (indexed.distinct nonnegative bound iNonnegative iBound same)
        simp only [exchange, atRight, atLeft, ite_false]
        rw [swap_positions heap layout i j _ separate]
        simpa [notRight, notLeft] using indexed.forward index nonnegative bound
  · intro vertex nonnegative
    by_cases isRight : vertex = heap.read layout.vertices j
    · subst vertex
      simp only [swap_positions heap layout i j _ separate, ite_true]
      exact ⟨iBound, by rw [swap_vertices heap layout i j i separate, exchange_left]⟩
    · by_cases isLeft : vertex = heap.read layout.vertices i
      · subst vertex
        simp only [swap_positions heap layout i j _ separate, isRight, ite_false, ite_true]
        exact ⟨jBound, by rw [swap_vertices heap layout i j j separate, exchange_right]⟩
      · have unchanged : (swapHeap heap layout i j).read layout.positions vertex =
            heap.read layout.positions vertex := by
          rw [swap_positions heap layout i j _ separate]
          simp [isRight, isLeft]
        rw [unchanged] at nonnegative ⊢
        obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
        have notRight : heap.read layout.positions vertex ≠ j := by
          intro same
          rw [same] at identity
          exact isRight identity.symm
        have notLeft : heap.read layout.positions vertex ≠ i := by
          intro same
          rw [same] at identity
          exact isLeft identity.symm
        refine ⟨bound, ?_⟩
        rw [swap_vertices heap layout i j _ separate]
        simpa [exchange, notRight, notLeft] using identity
  · intro vertex negative
    rw [swap_positions heap layout i j _ separate] at negative ⊢
    split at negative <;> simp_all
    · omega
    split at negative <;> simp_all
    · omega
    exact indexed.absent vertex negative

-- Position numbers may change, but exactly the same vertices remain present.
theorem swap_preserves_membership (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (iNonnegative : 0 ≤ i) (iBound : i < layout.size)
    (jNonnegative : 0 ≤ j) (jBound : j < layout.size) (vertex : Int) :
    0 ≤ (swapHeap heap layout i j).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex := by
  rw [swap_positions heap layout i j vertex separate]
  by_cases atRight : vertex = heap.read layout.vertices j
  · subst vertex
    simp [indexed.forward j jNonnegative jBound, iNonnegative, jNonnegative]
  · by_cases atLeft : vertex = heap.read layout.vertices i
    · subst vertex
      simp [atRight, indexed.forward i iNonnegative iBound, iNonnegative, jNonnegative]
    · simp [atRight, atLeft]

theorem swap_preserves_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (i j : Int) :
    layout.Valid (swapHeap heap layout i j) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩



-- Simple endpoint cases are checked against the compiled methods as well.






-- The mathematical depth is the prospective logarithmic bound. Each upward
-- move decreases it by exactly one; downward moves increase it by one.


theorem parent_bounds (index : Int) (positive : 0 < index) :
    0 ≤ Int.fdiv (index - 1) 2 ∧ Int.fdiv (index - 1) 2 < index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega





-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.






















































-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.










/-- Local parent comparisons imply that the root is a minimum of the active heap. -/
theorem Ordered.root_minimum {priority : Seq} {size : Int} (ordered : Ordered priority size)
    (index : Int) (nonnegative : 0 ≤ index) (within : index < size) :
    priority 0 ≤ priority index := by
  have result : ∀ n : Nat, (n : Int) < size → priority 0 ≤ priority (n : Int) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro bound
      by_cases zero : n = 0
      · subst n; exact Int.le_refl _
      · have positive : 0 < (n : Int) := by omega
        have bounds := parent_bounds (n : Int) positive
        have smaller : (parent (n : Int)).toNat < n := by
          unfold parent
          omega
        have parentBound : ((parent (n : Int)).toNat : Int) < size := by
          unfold parent
          omega
        have previous := ih _ smaller parentBound
        have parentCast : ((parent (n : Int)).toNat : Int) = parent (n : Int) :=
          Int.toNat_of_nonneg bounds.1
        rw [parentCast] at previous
        exact Int.le_trans previous (ordered _ positive bound)
  simpa [Int.toNat_of_nonneg nonnegative] using result index.toNat (by omega)











/-- A representation-level minimum statement, ready for an extraction contract. -/
theorem root_minimum_vertex (heap : Heap) (layout : Layout)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun position => heap.read layout.keys (heap.read layout.vertices position))
      layout.size)
    (vertex : Int) (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex := by
  obtain ⟨bound, identity⟩ := indexed.backward vertex present
  have minimum := ordered.root_minimum (heap.read layout.positions vertex) present bound
  simpa [identity] using minimum





-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.


















-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.


-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.




theorem OtherStoragePreserved.trans {first second third : Heap}
    (initial : OtherStoragePreserved first second)
    (remaining : OtherStoragePreserved second third) : OtherStoragePreserved first third :=
  ⟨remaining.nextRef.trans initial.nextRef, remaining.nextObject.trans initial.nextObject,
    remaining.objects.trans initial.objects, remaining.nextCollection.trans initial.nextCollection,
    remaining.collections.trans initial.collections⟩

-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.


-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.


















































/-- Replacing the root and shortening an ordered active prefix establishes
    sift-down's precondition. This is the order argument for minimum removal. -/
theorem Ordered.replace_root {priority : Seq} {size shorter key : Int}
    (ordered : Ordered priority size) (shrink : shorter ≤ size) :
    DownInvariant (fun index => if index = 0 then key else priority index) shorter 0 := by
  constructor
  · intro child positive bound parentNotRoot
    have childNotRoot : child ≠ 0 := by omega
    simpa [childNotRoot, parentNotRoot] using ordered child positive (by omega)
  · intro child positive bound fromIndex rootPositive
    omega

/-- Only the active prefix matters when moving between an abstract priority
    function and its concrete heap-array representation. -/
theorem DownInvariant.congr {first second : Seq} {size index : Int}
    (invariant : DownInvariant first size index) (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    DownInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive



-- Sift-down first selects the smaller child, then compares it with the parent.


























-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.


-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.
theorem sift_down_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_down.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ 2 * (depth (layout.size - 1) - depth index) ∧
      Heap.cost heap after "heap_swaps" ≤ depth (layout.size - 1) - depth index ∧
      (DownInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, membership, otherClocks, storage⟩ :=
    sift_down_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, membership, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_down.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega



theorem removed_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    { layout with size := layout.size - 1 }.Valid (removedHeap heap queue layout) queue := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 (layout.size - 1)
  constructor
  · change is_MinHeap (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue
      (layout.size - 1)) queue
    simpa [is_MinHeap, set_MinHeap_size] using swappedValid.object
  · simp only [removedHeap, vertices_write]
    simpa [field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using swappedValid.readVertices
  · simp only [removedHeap, positions_write]
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  · simp only [removedHeap, keys_write]
    simpa [field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using swappedValid.readKeys
  · simpa [removedHeap] using field_MinHeap_size_set _ _ (layout.size - 1) swappedValid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem removed_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions) :
    (removedHeap heap queue layout).read layout.vertices index =
      exchange (heap.read layout.vertices) 0 (layout.size - 1) index := by
  have preserved : (removedHeap heap queue layout).read layout.vertices index =
      (swapHeap heap layout 0 (layout.size - 1)).read layout.vertices index := by
    simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write, separate]
  exact preserved.trans (swap_vertices heap layout 0 (layout.size - 1) index separate)

theorem removed_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int) :
    (removedHeap heap queue layout).read layout.positions vertex =
      if vertex = heap.read layout.vertices 0 then -1
      else (swapHeap heap layout 0 (layout.size - 1)).read layout.positions vertex := by
  simp [removedHeap, set_MinHeap_size, Heap.read, Heap.write]

/-- Removing the last entry of an indexed prefix preserves its inverse map.
    This purely mathematical lemma also covers a singleton prefix. -/
theorem Indexed.remove_last (vertices positions : Seq) (size : Int)
    (indexed : Indexed vertices positions size) (nonempty : 0 < size) :
    Indexed vertices (fun vertex => if vertex = vertices (size - 1) then -1 else positions vertex)
      (size - 1) := by
  have lastNonnegative : 0 ≤ size - 1 := by omega
  have lastBound : size - 1 < size := by omega
  constructor
  · intro index nonnegative bound
    have notLast : vertices index ≠ vertices (size - 1) := by
      intro same
      have equal := indexed.distinct nonnegative (by omega) lastNonnegative lastBound same
      omega
    simpa [notLast] using indexed.forward index nonnegative (by omega)
  · intro vertex nonnegative
    have notLast : vertex ≠ vertices (size - 1) := by
      intro same
      simp [same] at nonnegative
    simp only [notLast, ite_false] at nonnegative ⊢
    obtain ⟨bound, identity⟩ := indexed.backward vertex nonnegative
    have different : positions vertex ≠ size - 1 := by
      intro same
      rw [same] at identity
      exact notLast identity.symm
    exact ⟨by omega, identity⟩
  · intro vertex negative
    by_cases same : vertex = vertices (size - 1)
    · simp [same]
    · simp only [same, ite_false] at negative ⊢
      exact indexed.absent vertex negative

/-- Shrinking after the swap removes exactly one entry and preserves all
    inverse-map invariants, before heap order is repaired by sift-down. -/
theorem removed_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) :
    Indexed ((removedHeap heap queue layout).read layout.vertices)
      ((removedHeap heap queue layout).read layout.positions) (layout.size - 1) := by
  let swapped := swapHeap heap layout 0 (layout.size - 1)
  have swappedIndexed : Indexed (swapped.read layout.vertices) (swapped.read layout.positions)
      layout.size :=
    swap_preserves_indexed heap layout 0 (layout.size - 1) valid.verticesPositions indexed
      (by omega) nonempty (by omega) (by omega)
  have last : swapped.read layout.vertices (layout.size - 1) = heap.read layout.vertices 0 := by
    simp [swapped, swap_vertices heap layout 0 (layout.size - 1) _ valid.verticesPositions]
  have vertices : (removedHeap heap queue layout).read layout.vertices =
      swapped.read layout.vertices := by
    funext index
    rw [removed_vertices heap queue layout index valid.verticesPositions]
    exact (swap_vertices heap layout 0 (layout.size - 1) index valid.verticesPositions).symm
  have positions : (removedHeap heap queue layout).read layout.positions =
      fun vertex => if vertex = swapped.read layout.vertices (layout.size - 1) then -1
        else swapped.read layout.positions vertex := by
    funext vertex
    rw [removed_positions, last]
  rw [vertices, positions]
  exact swappedIndexed.remove_last _ _ _ nonempty

/-- Membership after removal is old membership excluding the old root. -/
theorem removed_membership (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonempty : 0 < layout.size) (vertex : Int) :
    0 ≤ (removedHeap heap queue layout).read layout.positions vertex ↔
      0 ≤ heap.read layout.positions vertex ∧ vertex ≠ heap.read layout.vertices 0 := by
  rw [removed_positions]
  by_cases same : vertex = heap.read layout.vertices 0
  · simp [same]
  · simpa [same] using
      swap_preserves_membership heap layout 0 (layout.size - 1) valid.verticesPositions
        indexed (by omega) nonempty (by omega) (by omega) vertex

theorem removed_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (removedHeap heap queue layout).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm separateVertices, Ne.symm separatePositions]

theorem removed_read_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (ref : SeqRef) (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions)
    (index : Int) :
    (removedHeap heap queue layout).read ref index = heap.read ref index := by
  simp [removedHeap, swapHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions]



theorem removed_clocks_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (name : String) (notSwaps : name ≠ "heap_swaps") :
    (removedHeap heap queue layout).clocks name = heap.clocks name := by
  change (heap.tick "heap_swaps").clocks name = heap.clocks name
  exact Heap.clocks_tick_other heap "heap_swaps" name notSwaps

/-- Removing from a queue of at least two vertices composes a single swap and
    the supplied sift-down summary. The returned vertex is the original root. -/
theorem pop_with_sift_summary (heap after : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (multiple : 1 < layout.size)
    (sift : MinHeap.sift_down.Call (removedHeap heap queue layout) (queue, 0) after ()) :
    MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize]; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 (layout.size - 1)).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [swapHeap, set_MinHeap_size, field_MinHeap_positions, is_MinHeap,
      valid.object, valid.readPositions] using!
      show (field_MinHeap_positions heap queue).isSome = true ∧
        (field_MinHeap_positions heap queue).getD 0 < heap.nextRef from
      by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_true _ _ _ (by simp; omega))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc5 _ _ _
    (by change is_MinHeap (set_MinHeap_size
          (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue
        simpa [is_MinHeap, set_MinHeap_size] using
          (swap_preserves_layout heap queue layout valid 0 (layout.size - 1)).object))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc3 _ _ _)
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 (layout.size - 1)) queue (layout.size - 1)) queue =
      some layout.positions := by
    simpa [field_MinHeap_positions, set_MinHeap_size, is_MinHeap] using! valid.readPositions
  simp only [positions, Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)

/-- The public representation immediately supplies the root's minimum contract. -/
theorem QueueRep.root_minimum {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (vertex : Int)
    (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex :=
  root_minimum_vertex heap layout representation.indexed representation.ordered vertex present





/-- On the shortened active prefix, root removal replaces only the root's
    priority. Existing descendants retain their old ordering. -/
theorem removed_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (multiple : 1 < layout.size) :
    DownInvariant (fun index => (removedHeap heap queue layout).read layout.keys
      ((removedHeap heap queue layout).read layout.vertices index)) (layout.size - 1) 0 := by
  apply (ordered.replace_root (shorter := layout.size - 1)
    (key := heap.read layout.keys (heap.read layout.vertices (layout.size - 1))) (by omega)).congr (by omega)
  intro index nonnegative bound
  rw [removed_keys heap queue layout _ valid.verticesKeys valid.positionsKeys,
    removed_vertices heap queue layout index valid.verticesPositions]
  have notLast : index ≠ layout.size - 1 := by omega
  have rootNotLast : (0 : Int) ≠ layout.size - 1 := by omega
  by_cases root : index = 0 <;> simp [exchange, root, notLast, rootNotLast]





/-- For a larger queue, the caller supplies sift-down's proved contract after
    the root/last exchange. The proof never inspects sift-down transitions. -/
theorem pop_multiple_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (multiple : 1 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  let prepared := removedHeap heap queue layout
  let shorter := { layout with size := layout.size - 1 }
  have valid : shorter.Valid prepared queue := removed_layout heap queue layout representation.valid
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) shorter.size :=
    removed_indexed heap queue layout representation.valid representation.indexed (by omega)
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_down_summary prepared queue shorter 0 valid indexed (by omega) (by dsimp [shorter]; omega)
  refine ⟨after, pop_with_sift_summary heap after queue layout representation.valid multiple sift, ?_⟩
  constructor
  · refine ⟨afterValid, by dsimp [shorter]; omega, afterIndexed, ?_⟩
    exact repair (removed_order heap queue layout representation.valid representation.ordered multiple)
  · rw [representation.indexed.forward 0 (by omega) (by omega)]
    omega
  · exact representation.root_minimum
  · intro value
    rw [membership value]
    exact removed_membership heap queue layout representation.valid representation.indexed (by omega) value
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact removed_keys heap queue layout value representation.valid.verticesKeys representation.valid.positionsKeys
  · simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
      set_MinHeap_size, shorter, depth, Int.sub_sub] using! comparisons
  · have bound : after.clocks "heap_swaps" - (heap.clocks "heap_swaps" + 1) ≤
        depth (layout.size - 2) := by
      simpa [Heap.cost, prepared, removedHeap, swapHeap, Heap.tick, Heap.write,
        set_MinHeap_size, shorter, depth, Int.sub_sub] using! swaps
    unfold Heap.cost
    omega
  · intro ref notVertices notPositions index
    rw [unchanged ref notVertices notPositions index]
    exact removed_read_other heap queue layout ref notVertices notPositions index
  · intro name notComparisons notSwaps
    rw [clocks name notComparisons notSwaps]
    exact removed_clocks_other heap queue layout name notSwaps
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size - 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage







end BinaryModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        LT.lt.{0} (1 : Int) layout.size →
          Exists.{1} fun after =>
            Algo.indexed_heap.MinHeap.pop_min.Call heap queue after
                (heap.read layout.vertices (0 : Int)) ∧
              BinaryModuleAnalysis.Extracted heap after queue layout
                (heap.read layout.vertices (0 : Int)) :=
  BinaryModuleAnalysis.pop_multiple_correct
