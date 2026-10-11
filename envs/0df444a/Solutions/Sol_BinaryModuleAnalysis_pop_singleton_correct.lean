-- Prove2me | solution 1 for BinaryModuleAnalysis.pop_singleton_correct
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:53.086983+00:00
-- url     : https://prove2.me/submissions/0f295d96-251b-44de-8995-7aa378324750

import Definitions.Def_Algo_indexed_heap_Analysis


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



theorem swap_cost (heap : Heap) (layout : Layout) (i j : Int) :
    Heap.cost heap (swapHeap heap layout i j) = Clocks.single "heap_swaps" 1 := by
  funext name
  by_cases swaps : name = "heap_swaps"
  · subst name
    simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single]
  · simp [swapHeap, Heap.cost, Heap.tick, Heap.write, Clocks.single, swaps]

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










































theorem pop_singleton_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (singleton : layout.size = 1) :
    MinHeap.pop_min.Call heap queue (poppedHeap heap queue layout)
      (heap.read layout.vertices 0) := by
  have swappedValid := swap_preserves_layout heap queue layout valid 0 0
  have positions : field_MinHeap_positions
      (set_MinHeap_size (swapHeap heap layout 0 0) queue 0) queue = some layout.positions := by
    simpa [field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using swappedValid.readPositions
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pop_min_pc21 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc20_false _ _ _ (by simp [valid.readSize, singleton]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc17 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc16 _ _ _ (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc14 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc12 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc11 _ _ _)
  simp only [valid.readSize, valid.readVertices, Option.getD_some, singleton, Int.sub_self]
  apply Reaches.trans ((swap_summary heap queue layout valid 0 0).2 _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc10 _ _ _ swappedValid.object)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc9 _ _ _
    (by simpa [positions] using! swappedValid.positionsAllocated))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pop_min_pc7_false _ _ _ (by simp))
  apply Reaches.prepend (Step.MinHeap_pop_min_pc2 _ _ _)
  simp only [positions, Option.getD_some]
  exact Reaches.single (Step.MinHeap_pop_min_pc1 _ _ _)











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






-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.


-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.
























































-- Sift-down first selects the smaller child, then compares it with the parent.


























-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.


-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.




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

theorem removed_cost (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) :
    Heap.cost heap (removedHeap heap queue layout) = Clocks.single "heap_swaps" 1 := by
  exact swap_cost heap layout 0 (layout.size - 1)

theorem removed_clocks_other (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (name : String) (notSwaps : name ≠ "heap_swaps") :
    (removedHeap heap queue layout).clocks name = heap.clocks name := by
  change (heap.tick "heap_swaps").clocks name = heap.clocks name
  exact Heap.clocks_tick_other heap "heap_swaps" name notSwaps



/-- The public representation immediately supplies the root's minimum contract. -/
theorem QueueRep.root_minimum {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (representation : QueueRep heap queue layout) (vertex : Int)
    (present : 0 ≤ heap.read layout.positions vertex) :
    heap.read layout.keys (heap.read layout.vertices 0) ≤ heap.read layout.keys vertex :=
  root_minimum_vertex heap layout representation.indexed representation.ordered vertex present









/-- Extracting a singleton needs only its implemented self-swap. -/
theorem pop_singleton_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (singleton : layout.size = 1) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  have nonempty : 0 < layout.size := by omega
  have same : removedHeap heap queue layout = poppedHeap heap queue layout := by
    simp only [removedHeap, singleton, Int.sub_self, poppedHeap]
  refine ⟨removedHeap heap queue layout, ?_, ?_⟩
  · rw [same]
    exact pop_singleton_summary heap queue layout representation.valid singleton
  · constructor
    · refine ⟨removed_layout heap queue layout representation.valid, by simp [singleton],
        removed_indexed heap queue layout representation.valid representation.indexed nonempty, ?_⟩
      intro child positive bound
      change child < layout.size - 1 at bound
      omega
    · rw [representation.indexed.forward 0 (by omega) nonempty]
      omega
    · exact representation.root_minimum
    · exact removed_membership heap queue layout representation.valid representation.indexed nonempty
    · exact fun value => removed_keys heap queue layout value representation.valid.verticesKeys
        representation.valid.positionsKeys
    · rw [removed_cost]
      simp [Clocks.single]
    · rw [removed_cost]
      simp [Clocks.single]
    · exact removed_read_other heap queue layout
    · intro name _ notSwaps
      exact removed_clocks_other heap queue layout name notSwaps
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩









end BinaryModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        Eq.{1} layout.size (1 : Int) →
          Exists.{1} fun after =>
            Algo.indexed_heap.MinHeap.pop_min.Call heap queue after
                (heap.read layout.vertices (0 : Int)) ∧
              BinaryModuleAnalysis.Extracted heap after queue layout
                (heap.read layout.vertices (0 : Int)) :=
  BinaryModuleAnalysis.pop_singleton_correct
