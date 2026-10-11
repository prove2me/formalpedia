-- Prove2me | solution 1 for BinaryModuleAnalysis.sift_down_loop
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:52.471531+00:00
-- url     : https://prove2.me/submissions/9ff48e68-4be1-48c9-adef-e7fbab9ee468

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

theorem swap_keys (heap : Heap) (layout : Layout) (i j vertex : Int)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (swapHeap heap layout i j).read layout.keys vertex = heap.read layout.keys vertex := by
  simp [swapHeap, Heap.read, Heap.write, Ne.symm separateVertices, Ne.symm separatePositions]



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



theorem child_depth (index child : Int) (nonnegative : 0 ≤ index)
    (isChild : child = 2 * index + 1 ∨ child = 2 * index + 2) :
    depth child = depth index + 1 := by
  have offset : (child.toNat + 1) / 2 = index.toNat + 1 := by omega
  unfold depth
  rw [Nat.log2_def (child.toNat + 1), if_pos (by omega), offset]

-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.






















































-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.




















/-- The abstract priority exchange is exactly the effect of the compiled swap. -/
theorem swap_priorities (heap : Heap) (layout : Layout) (i j : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (swapHeap heap layout i j).read layout.keys
      ((swapHeap heap layout i j).read layout.vertices position)) =
    exchange (fun position => heap.read layout.keys (heap.read layout.vertices position)) i j := by
  funext position
  rw [swap_keys heap layout i j _ separateVertices separatePositions,
    swap_vertices heap layout i j position separate]
  simp only [exchange]
  split <;> simp_all
  split <;> simp_all







-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.










theorem Layout.Valid.tick {layout : Layout} {heap : Heap} {queue : Ref_MinHeap}
    (valid : layout.Valid heap queue) (name : String) (amount : Nat := 1) :
    layout.Valid (heap.tick name amount) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩







-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.


-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.


theorem OtherStoragePreserved.refl (heap : Heap) : OtherStoragePreserved heap heap :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

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














































/-- Once the moving entry is below both children (including a leaf), the
    entire active prefix is a heap. -/
theorem DownInvariant.finish {priority : Seq} {size index : Int}
    (invariant : DownInvariant priority size index)
    (orderedChildren : ∀ child, 0 < child → child < size → parent child = index →
      priority index ≤ priority child) :
    Ordered priority size := by
  intro child positive bound
  by_cases fromIndex : parent child = index
  · simpa [fromIndex] using orderedChildren child positive bound fromIndex
  · exact invariant.orderedExcept child positive bound fromIndex

/-- A smaller minimum child can be promoted, moving the only possible disorder
    down one level. The sibling edge and all ancestor edges remain ordered. -/
theorem DownInvariant.exchange_minimum {priority : Seq} {size index chosen : Int}
    (invariant : DownInvariant priority size index)
    (chosenPositive : 0 < chosen) (chosenBound : chosen < size)
    (fromIndex : parent chosen = index)
    (smaller : priority chosen < priority index)
    (minimum : ∀ child, 0 < child → child < size → parent child = index →
      priority chosen ≤ priority child) :
    DownInvariant (exchange priority index chosen) size chosen := by
  have indexSmaller : index < chosen := by
    have bounds : parent chosen < chosen := (parent_bounds chosen chosenPositive).2
    omega
  have different : index ≠ chosen := by omega
  constructor
  · intro child positive bound notChosen
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    by_cases atIndex : child = index
    · subst child
      have parentNotIndex : parent index ≠ index := by omega
      have parentNotChosen : parent index ≠ chosen := by omega
      have old := invariant.parentBelowChildren chosen chosenPositive chosenBound fromIndex positive
      simpa [exchange, parentNotIndex, parentNotChosen, different] using old
    · by_cases atChosen : child = chosen
      · subst child
        rw [fromIndex, exchange_left, exchange_right]
        exact Int.le_of_lt smaller
      · by_cases parentIndex : parent child = index
        · have old := minimum child positive bound parentIndex
          simpa [exchange, atIndex, atChosen, parentIndex, different] using old
        · simpa [exchange, atIndex, atChosen, parentIndex, notChosen] using
            invariant.orderedExcept child positive bound parentIndex
  · intro child positive bound parentChosen _
    have bounds : parent child < child := (parent_bounds child positive).2
    have childNotIndex : child ≠ index := by omega
    have childNotChosen : child ≠ chosen := by omega
    have old := invariant.orderedExcept child positive bound (by omega)
    rw [parentChosen] at old
    simpa [exchange, fromIndex, different, childNotIndex, childNotChosen] using old





/-- Binary-tree parents give exactly the source's two child positions. -/
theorem parent_children (index child : Int) :
    parent child = index ↔ child = 2 * index + 1 ∨ child = 2 * index + 2 := by
  unfold parent
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

-- Sift-down first selects the smaller child, then compares it with the parent.








theorem sift_down_stop (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (leaf : layout.size ≤ 2 * index + 1) :
    MinHeap.sift_down.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_false _ _ _
      (by simp [valid.readSize]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc1 _ _ _)

theorem sift_down_select (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftDown state queue index)
    (valid : layout.Valid state.heap queue) (hasChild : 2 * index + 1 < layout.size)
    (remaining : ∀ nextState,
      AtChildComparison nextState queue index (selectedChild state.heap layout index) →
      nextState.heap = state.heap.tick "heap_comparisons" (selectionComparisons layout index) →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_down.At.down_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc4 _ _ _ (by simp [valid.readSize]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc3_true _ _ _ (by simp [valid.readSize, hasChild]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc23 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc22 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc21 _ _ _ (by simp [valid.readSize]))
    by_cases rightPresent : 2 * s.v1 + 2 < layout.size
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_true _ _ _
        (by simp [valid.readSize]; omega))
      apply Reaches.prepend (Step.MinHeap_sift_down_pc19 _ _ _)
      apply Reaches.prepend (Step.MinHeap_sift_down_pc18 _ _ _
        (by simp [valid.readKeys, valid.readVertices, valid.keysAllocated, valid.verticesAllocated]))
      by_cases rightSmaller : heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
          heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_true _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        apply Reaches.prepend (Step.MinHeap_sift_down_pc16 _ _ _)
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 2
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
      · apply Reaches.prepend (Step.MinHeap_sift_down_pc17_false _ _ _
          (by simpa [valid.readKeys, valid.readVertices, Int.add_assoc] using rightSmaller))
        let nextState : Configuration := .active (heap.tick "heap_comparisons")
          (.fn_MinHeap_sift_down 15 { s with
            v2 := 2 * s.v1 + 1
            v3 := 2 * s.v1 + 2
            t5 := decide (2 * s.v1 + 1 < layout.size)
            t12 := decide (2 * s.v1 + 2 < layout.size)
            t13 := decide (heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 2)) <
              heap.read layout.keys (heap.read layout.vertices (2 * s.v1 + 1))) }) originalStack
        have finish := remaining nextState
          (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
            MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
            selectedChild, rightPresent, rightSmaller, Config.heap])
          (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
        simpa [nextState, valid.readSize, valid.readKeys, valid.readVertices, Int.add_assoc] using finish stack
    · apply Reaches.prepend (Step.MinHeap_sift_down_pc20_false _ _ _
        (by simp [valid.readSize]; omega))
      let nextState : Configuration := .active heap
        (.fn_MinHeap_sift_down 15 { s with
          v2 := 2 * s.v1 + 1
          v3 := 2 * s.v1 + 2
          t5 := decide (2 * s.v1 + 1 < layout.size)
          t12 := decide (2 * s.v1 + 2 < layout.size) }) originalStack
      have finish := remaining nextState
        (by simp [AtChildComparison, nextState, MinHeap.sift_down.At.compare_child,
          MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i, MinHeap.sift_down.Local.child,
          selectedChild, rightPresent, Config.heap])
        (by simp [nextState, selectionComparisons, rightPresent, Config.heap])
      simpa [nextState, valid.readSize, Int.add_assoc] using finish stack

theorem sift_down_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child)) :
    MinHeap.sift_down.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_down_pc11 _ _ _)

theorem sift_down_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index child : Int) (finalHeap : Heap) (location : AtChildComparison state queue index child)
    (valid : layout.Valid state.heap queue)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices index) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices child))
    (remaining : ∀ nextState, AtSiftDown nextState queue child →
      nextState.heap = swapHeap (state.heap.tick "heap_comparisons") layout index child →
      MinHeap.sift_down.CallFrom nextState finalHeap ()) :
    MinHeap.sift_down.CallFrom state finalHeap () := by
  rcases location with ⟨atCompare, readSelf, readIndex, readChild⟩
  cases state with
  | done => cases atCompare
  | active heap frame originalStack =>
    cases frame <;> try { cases atCompare }
    rename_i pc s
    have counter : pc = 15 := by
      unfold MinHeap.sift_down.At.compare_child at atCompare
      split at atCompare <;> simp_all
    subst pc
    simp [MinHeap.sift_down.Local.self, MinHeap.sift_down.Local.i,
      MinHeap.sift_down.Local.child] at readSelf readIndex readChild
    cases readSelf
    cases readIndex
    cases readChild
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices s.v1) ≤
      heap.read layout.keys (heap.read layout.vertices s.v2) at unordered
    let nextState : Configuration := .active
      (swapHeap (heap.tick "heap_comparisons") layout s.v1 s.v2)
      (.fn_MinHeap_sift_down 4 { s with
        v1 := s.v2
        t6 := ()
        t7 := s.v0
        t8 := s.v1
        t9 := s.v2
        t10 := decide (heap.read layout.keys (heap.read layout.vertices s.v1) ≤
          heap.read layout.keys (heap.read layout.vertices s.v2)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_down_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_down_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 s.v2).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_down_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using finish stack

theorem selectedChild_bounds (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) (hasChild : 2 * index + 1 < layout.size) :
    0 < selectedChild heap layout index ∧ selectedChild heap layout index < layout.size ∧
      parent (selectedChild heap layout index) = index := by
  unfold selectedChild
  split
  · rename_i chosen
    refine ⟨by omega, chosen.1, ?_⟩
    rw [parent_children]
    exact Or.inr rfl
  · refine ⟨by omega, hasChild, ?_⟩
    rw [parent_children]
    exact Or.inl rfl

theorem selectedChild_minimum (heap : Heap) (layout : Layout) (index child : Int)
    (childBound : child < layout.size) (childOf : parent child = index) :
    heap.read layout.keys (heap.read layout.vertices (selectedChild heap layout index)) ≤
      heap.read layout.keys (heap.read layout.vertices child) := by
  have options := (parent_children index child).mp childOf
  rcases options with rfl | rfl <;> unfold selectedChild <;> split <;> rename_i selected
  · exact Int.le_of_lt selected.2
  · exact Int.le_refl _
  · exact Int.le_refl _
  · have notSmaller : ¬ heap.read layout.keys (heap.read layout.vertices (2 * index + 2)) <
        heap.read layout.keys (heap.read layout.vertices (2 * index + 1)) := by
      intro smaller
      exact selected ⟨childBound, smaller⟩
    omega

theorem depth_mono {first second : Int} (ordered : first ≤ second) : depth first ≤ depth second := by
  unfold depth
  apply (Nat.le_log2 (by omega)).2
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem selectedChild_depth (heap : Heap) (layout : Layout) (index : Int)
    (nonnegative : 0 ≤ index) :
    depth (selectedChild heap layout index) = depth index + 1 := by
  apply child_depth index _ nonnegative
  unfold selectedChild
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem selectionComparisons_bound (layout : Layout) (index : Int) :
    selectionComparisons layout index ≤ 1 := by
  unfold selectionComparisons
  split <;> decide

-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.
theorem sift_down_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftDown state queue index → state.heap = heap →
        MinHeap.sift_down.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" +
        2 * (depth (layout.size - 1) - depth index) ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" +
        (depth (layout.size - 1) - depth index) ∧
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
  generalize rankEq : depth (layout.size - 1) - depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases hasChild : 2 * index + 1 < layout.size
    · let child := selectedChild heap layout index
      let comparedHeap := (heap.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      have childFacts := selectedChild_bounds heap layout index nonnegative hasChild
      have childDepth := selectedChild_depth heap layout index nonnegative
      have depthBound : depth child ≤ depth (layout.size - 1) := depth_mono (by dsimp [child]; omega)
      have selectionBound := selectionComparisons_bound layout index
      have comparedValid : layout.Valid comparedHeap queue :=
        (valid.tick "heap_comparisons" (selectionComparisons layout index)).tick "heap_comparisons"
      by_cases ordered : heap.read layout.keys (heap.read layout.vertices index) ≤
          heap.read layout.keys (heap.read layout.vertices child)
      · refine ⟨comparedHeap, ?_, comparedValid, indexed, ?_, ?_, ?_, ?_, ?_, ?_,
          ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index comparedHeap location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          have location' : AtChildComparison compareState queue index child := by
            simpa [sameHeap, child] using compareLocation
          have valid' : layout.Valid compareState.heap queue := by
            simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index)
          have ordered' : compareState.heap.read layout.keys (compareState.heap.read layout.vertices index) ≤
              compareState.heap.read layout.keys (compareState.heap.read layout.vertices child) := by
            simpa [compareHeap, sameHeap] using ordered
          simpa [comparedHeap, compareHeap, sameHeap] using
            sift_down_ordered compareState queue layout index child location' valid' ordered'
        · simp only [comparedHeap, Heap.clocks_tick_same]
          dsimp [child] at depthBound
          omega
        · simp [comparedHeap, Heap.tick]
        · intro invariant
          apply invariant.finish
          intro descendant _ descendantBound childOf
          exact Int.le_trans ordered (selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref _ _ position
          rfl
        · intro vertex
          rfl
        · intro name notComparisons _
          simp [comparedHeap, Heap.tick, notComparisons]
      · let nextHeap := swapHeap comparedHeap layout index child
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout comparedHeap queue layout comparedValid index child
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed comparedHeap layout index child valid.verticesPositions indexed
            nonnegative bound (by dsimp [child]; omega) childFacts.2.1
        have smaller : depth (layout.size - 1) - depth child < rank := by
          dsimp [child] at depthBound ⊢
          omega
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, membership, otherClocks, storage⟩ :=
          inductionHypothesis (depth (layout.size - 1) - depth child) smaller nextHeap child
            nextValid nextIndexed (by dsimp [child]; omega) childFacts.2.1 rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_down_select state queue layout index after location
            (by simpa [sameHeap] using valid) hasChild
          intro compareState compareLocation compareHeap
          apply sift_down_continue compareState queue layout index child after
            (by simpa [sameHeap, child] using compareLocation)
            (by simpa [compareHeap, sameHeap] using
              valid.tick "heap_comparisons" (selectionComparisons layout index))
            (by simpa [compareHeap, sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [nextHeap, comparedHeap, compareHeap, sameHeap] using nextHeapEq
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          dsimp [child] at comparisons depthBound
          omega
        · simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write] at swaps
          dsimp [child] at swaps depthBound
          omega
        · intro invariant
          apply repair
          change DownInvariant (fun position => (swapHeap comparedHeap layout index child).read layout.keys
            ((swapHeap comparedHeap layout index child).read layout.vertices position)) layout.size child
          rw [swap_priorities comparedHeap layout index child valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_minimum childFacts.1 childFacts.2.1 childFacts.2.2
            (by omega) (fun descendant _ descendantBound childOf =>
              selectedChild_minimum heap layout index descendant descendantBound childOf)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          simp [nextHeap, comparedHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]
        · intro vertex
          rw [membership vertex]
          exact swap_preserves_membership comparedHeap layout index child valid.verticesPositions
            indexed nonnegative bound (by dsimp [child]; omega) childFacts.2.1 vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, comparedHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_down_stop state queue layout index location
          (by simpa [sameHeap] using valid) (by omega)
      · intro invariant
        apply invariant.finish
        intro child _ childBound childOf
        have children := (parent_children index child).mp childOf
        omega
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.














































end BinaryModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout) (index : Int),
      layout.Valid heap queue →
        BinaryModuleAnalysis.Indexed (heap.read layout.vertices) (heap.read layout.positions)
            layout.size →
          LE.le.{0} (0 : Int) index →
            LT.lt.{0} index layout.size →
              Exists.{1} fun after =>
                (∀ (state : Algo.indexed_heap.Algo2LeanGenerated.Configuration),
                    BinaryModuleAnalysis.AtSiftDown state queue index →
                      Eq.{1} (Algo2LeanCore.Config.heap.{0, 0, 0} state) heap →
                        Algo.indexed_heap.MinHeap.sift_down.CallFrom state after ()) ∧
                  layout.Valid after queue ∧
                    BinaryModuleAnalysis.Indexed (after.read layout.vertices)
                        (after.read layout.positions) layout.size ∧
                      LE.le.{0} (after.clocks "heap_comparisons")
                          (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_comparisons")
                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                              (HSub.hSub.{0, 0, 0}
                                (BinaryModuleAnalysis.depth (HSub.hSub.{0, 0, 0} layout.size (1 : Int)))
                                (BinaryModuleAnalysis.depth index)))) ∧
                        LE.le.{0} (after.clocks "heap_swaps")
                            (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_swaps")
                              (HSub.hSub.{0, 0, 0}
                                (BinaryModuleAnalysis.depth (HSub.hSub.{0, 0, 0} layout.size (1 : Int)))
                                (BinaryModuleAnalysis.depth index))) ∧
                          (BinaryModuleAnalysis.DownInvariant
                                (fun position =>
                                  heap.read layout.keys (heap.read layout.vertices position))
                                layout.size index →
                              BinaryModuleAnalysis.Ordered
                                (fun position =>
                                  after.read layout.keys (after.read layout.vertices position))
                                layout.size) ∧
                            (∀ (ref : Algo2LeanGenerated.SeqRef),
                                Ne.{1} ref layout.vertices →
                                  Ne.{1} ref layout.positions →
                                    ∀ (position : Int),
                                      Eq.{1} (after.read ref position) (heap.read ref position)) ∧
                              (∀ (vertex : Int),
                                  LE.le.{0} (0 : Int) (after.read layout.positions vertex) ↔
                                    LE.le.{0} (0 : Int) (heap.read layout.positions vertex)) ∧
                                (∀ (name : String),
                                    Ne.{1} name "heap_comparisons" →
                                      Ne.{1} name "heap_swaps" →
                                        Eq.{1} (after.clocks name) (heap.clocks name)) ∧
                                  BinaryModuleAnalysis.OtherStoragePreserved heap after :=
  BinaryModuleAnalysis.sift_down_loop
