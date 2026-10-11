-- Prove2me | solution 1 for BinaryModuleAnalysis.sift_up_loop
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:51.426748+00:00
-- url     : https://prove2.me/submissions/56472271-9bd5-4945-80ca-34f042531c87

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

theorem parent_depth (index : Int) (positive : 0 < index) :
    depth (Int.fdiv (index - 1) 2) + 1 = depth index := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  have offset : ((index - 1) / 2).toNat + 1 = (index.toNat + 1) / 2 := by omega
  unfold depth
  rw [offset, Nat.log2_def (index.toNat + 1), if_pos (by omega)]



-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.






















































-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.














/-- Once the exceptional edge is ordered (or the root is reached), sift-up is done. -/
theorem UpInvariant.finish {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (done : index ≤ 0 ∨ priority (parent index) ≤ priority index) :
    Ordered priority size := by
  intro child positive bound
  by_cases same : child = index
  · subst child
    rcases done with nonpositive | ordered
    · omega
    · exact ordered
  · exact invariant.orderedExcept child positive bound same

/-- Exchanging an out-of-order position with its parent moves the single
    exceptional edge up one level; every other heap-order edge stays valid. -/
theorem UpInvariant.exchange_parent {priority : Seq} {size index : Int}
    (invariant : UpInvariant priority size index)
    (positive : 0 < index) (within : index < size)
    (outOfOrder : priority index < priority (parent index)) :
    UpInvariant (exchange priority index (parent index)) size (parent index) := by
  have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index positive
  have different : index ≠ parent index := by omega
  constructor
  · intro child childPositive childBound notParent
    by_cases atIndex : child = index
    · subst child
      rw [exchange_right, exchange_left]
      exact Int.le_of_lt outOfOrder
    · by_cases fromIndex : parent child = index
      · have below := invariant.parentBelowChildren child childPositive childBound fromIndex positive
        simpa [exchange, fromIndex, atIndex, notParent, different, Ne.symm different] using below
      · by_cases fromParent : parent child = parent index
        · have old := invariant.orderedExcept child childPositive childBound atIndex
          rw [fromParent] at old
          simpa [exchange, fromParent, atIndex, notParent] using
            Int.le_trans (Int.le_of_lt outOfOrder) old
        · simpa [exchange, fromIndex, fromParent, atIndex, notParent] using
            invariant.orderedExcept child childPositive childBound atIndex
  · intro child childPositive childBound fromParent parentPositive
    have ancestorBounds : 0 ≤ parent (parent index) ∧ parent (parent index) < parent index :=
      parent_bounds (parent index) parentPositive
    have ancestorNotParent : parent (parent index) ≠ parent index := by omega
    have ancestorNotIndex : parent (parent index) ≠ index := by omega
    have childBounds : parent child < child := (parent_bounds child childPositive).2
    have notParent : child ≠ parent index := by omega
    have oldParent := invariant.orderedExcept (parent index) parentPositive (by omega) (by omega)
    by_cases atIndex : child = index
    · subst child
      simpa [exchange, ancestorNotParent, ancestorNotIndex, different] using oldParent
    · have oldChild := invariant.orderedExcept child childPositive childBound atIndex
      rw [fromParent] at oldChild
      simpa [exchange, ancestorNotParent, ancestorNotIndex, notParent, atIndex] using
        Int.le_trans oldParent oldChild



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






theorem sift_up_stop (state : Configuration) (queue : Ref_MinHeap) (index : Int)
    (location : AtSiftUp state queue index) (atRoot : index ≤ 0) :
    MinHeap.sift_up.CallFrom state state.heap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_false _ _ _
      (by simp only [decide_eq_false_iff_not]; omega))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc2 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc1 _ _ _)

theorem sift_up_ordered (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (ordered : state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index)) :
    MinHeap.sift_up.CallFrom state (state.heap.tick "heap_comparisons") () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at ordered
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_true _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using ordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc12 _ _ _)
    exact Reaches.single (Step.MinHeap_sift_up_pc11 _ _ _)

theorem Layout.Valid.tick {layout : Layout} {heap : Heap} {queue : Ref_MinHeap}
    (valid : layout.Valid heap queue) (name : String) (amount : Nat := 1) :
    layout.Valid (heap.tick name amount) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩



theorem upHeap_priorities (heap : Heap) (layout : Layout) (index : Int)
    (separate : layout.vertices ≠ layout.positions)
    (separateVertices : layout.vertices ≠ layout.keys)
    (separatePositions : layout.positions ≠ layout.keys) :
    (fun position => (upHeap heap layout index).read layout.keys
      ((upHeap heap layout index).read layout.vertices position)) =
      exchange (fun position => heap.read layout.keys (heap.read layout.vertices position))
        index (parent index) := by
  simpa [upHeap, parent] using swap_priorities (heap.tick "heap_comparisons") layout
    index (parent index) separate separateVertices separatePositions

theorem upHeap_read_other (heap : Heap) (layout : Layout) (index : Int)
    (ref : SeqRef) (position : Int)
    (notVertices : ref ≠ layout.vertices) (notPositions : ref ≠ layout.positions) :
    (upHeap heap layout index).read ref position = heap.read ref position := by
  simp [upHeap, swapHeap, Heap.read, Heap.write, notVertices, notPositions]

-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.
theorem sift_up_continue (state : Configuration) (queue : Ref_MinHeap) (layout : Layout)
    (index : Int) (finalHeap : Heap) (location : AtSiftUp state queue index)
    (valid : layout.Valid state.heap queue) (positive : 0 < index)
    (unordered : ¬ state.heap.read layout.keys (state.heap.read layout.vertices
        (Int.fdiv (index - 1) 2)) ≤
      state.heap.read layout.keys (state.heap.read layout.vertices index))
    (remaining : ∀ nextState, AtSiftUp nextState queue (Int.fdiv (index - 1) 2) →
      nextState.heap = upHeap state.heap layout index →
      MinHeap.sift_up.CallFrom nextState finalHeap ()) :
    MinHeap.sift_up.CallFrom state finalHeap () := by
  rcases location with ⟨atLoop, readSelf, readIndex⟩
  cases state with
  | done => cases atLoop
  | active heap frame originalStack =>
    cases frame <;> try { cases atLoop }
    rename_i pc s
    have counter : pc = 4 := by
      unfold MinHeap.sift_up.At.up_loop at atLoop
      split at atLoop <;> simp_all
    subst pc
    simp [MinHeap.sift_up.Local.self, MinHeap.sift_up.Local.i] at readSelf readIndex
    cases readSelf
    cases readIndex
    change layout.Valid heap s.v0 at valid
    change ¬ heap.read layout.keys (heap.read layout.vertices (Int.fdiv (s.v1 - 1) 2)) ≤
      heap.read layout.keys (heap.read layout.vertices s.v1) at unordered
    let parent := Int.fdiv (s.v1 - 1) 2
    let nextState : Configuration := .active (upHeap heap layout s.v1)
      (.fn_MinHeap_sift_up 4 { s with
        v1 := parent
        v2 := parent
        t4 := decide (s.v1 > 0)
        t5 := ()
        t6 := s.v0
        t7 := s.v1
        t8 := parent
        t9 := decide (heap.read layout.keys (heap.read layout.vertices parent) ≤
          heap.read layout.keys (heap.read layout.vertices s.v1)) }) originalStack
    have finish := remaining nextState ⟨True.intro, rfl, rfl⟩ rfl
    intro stack
    apply Reaches.prepend (Step.MinHeap_sift_up_pc4 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc3_true _ _ _ (by simp [positive]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc16 _ _ _ (by decide))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc15 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc14 _ _ _
      (by simp [valid.readKeys, valid.readVertices, valid.verticesAllocated, valid.keysAllocated]))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc13_false _ _ _
      (by simpa [valid.readKeys, valid.readVertices] using unordered))
    apply Reaches.prepend (Step.MinHeap_sift_up_pc10 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc9 _ _ _ valid.object)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc8 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc7 _ _ _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc6 _ _ _)
    apply Reaches.trans ((swap_summary (heap.tick "heap_comparisons") s.v0 layout
      (valid.tick "heap_comparisons") s.v1 parent).2 _)
    apply Reaches.prepend (Step.MinHeap_sift_up_pc5 _ _ _)
    simpa only [keys_tick, vertices_tick, valid.readKeys, valid.readVertices,
      Option.getD_some, Heap.read_tick] using! finish stack

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
theorem sift_up_loop (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after,
      (∀ state, AtSiftUp state queue index → state.heap = heap →
        MinHeap.sift_up.CallFrom state after ()) ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      after.clocks "heap_comparisons" ≤ heap.clocks "heap_comparisons" + depth index ∧
      after.clocks "heap_swaps" ≤ heap.clocks "heap_swaps" + depth index ∧
      (UpInvariant (fun position => heap.read layout.keys (heap.read layout.vertices position))
        layout.size index →
        Ordered (fun position => after.read layout.keys (after.read layout.vertices position))
          layout.size) ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ∀ position,
        after.read ref position = heap.read ref position) ∧
      (∀ vertex, 0 ≤ after.read layout.positions vertex ↔ 0 ≤ heap.read layout.positions vertex) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved heap after := by
  generalize rankEq : depth index = rank
  induction rank using Nat.strongRecOn generalizing heap index with
  | ind rank inductionHypothesis =>
    by_cases positive : 0 < index
    · have parentFacts := parent_bounds index positive
      have depthChange := parent_depth index positive
      by_cases ordered : heap.read layout.keys
          (heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
          heap.read layout.keys (heap.read layout.vertices index)
      · refine ⟨heap.tick "heap_comparisons", ?_, valid.tick "heap_comparisons", indexed,
          ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · intro state location sameHeap
          have validState : layout.Valid state.heap queue := by simpa [sameHeap] using valid
          have orderedState : state.heap.read layout.keys
              (state.heap.read layout.vertices (Int.fdiv (index - 1) 2)) ≤
              state.heap.read layout.keys (state.heap.read layout.vertices index) := by
            simpa [sameHeap] using ordered
          simpa [sameHeap] using sift_up_ordered state queue layout index location
            validState positive orderedState
        · simp only [Heap.clocks_tick_same]
          omega
        · simp [Heap.tick]
        · intro invariant
          exact invariant.finish (Or.inr ordered)
        · intro ref _ _ position
          exact Heap.read_tick heap "heap_comparisons" 1 ref position
        · intro vertex
          rfl
        · intro name notComparisons _
          exact Heap.clocks_tick_other heap "heap_comparisons" name notComparisons
      · let nextHeap := upHeap heap layout index
        have nextValid : layout.Valid nextHeap queue :=
          swap_preserves_layout (heap.tick "heap_comparisons") queue layout
            (valid.tick "heap_comparisons") index (Int.fdiv (index - 1) 2)
        have nextIndexed : Indexed (nextHeap.read layout.vertices)
            (nextHeap.read layout.positions) layout.size :=
          swap_preserves_indexed (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed
            nonnegative bound parentFacts.1 (by omega)
        obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
            unchanged, presentIff, otherClocks, storage⟩ :=
          inductionHypothesis (depth (Int.fdiv (index - 1) 2)) (by omega)
            nextHeap (Int.fdiv (index - 1) 2) nextValid nextIndexed parentFacts.1 (by omega) rfl
        refine ⟨after, ?_, afterValid, afterIndexed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro state location sameHeap
          apply sift_up_continue state queue layout index after location
            (by simpa [sameHeap] using valid) positive (by simpa [sameHeap] using ordered)
          intro nextState nextLocation nextHeapEq
          apply remaining nextState nextLocation
          simpa [sameHeap, nextHeap] using nextHeapEq
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at comparisons
          omega
        · simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write] at swaps
          omega
        · intro invariant
          apply repair
          change UpInvariant (fun position => (upHeap heap layout index).read layout.keys
            ((upHeap heap layout index).read layout.vertices position)) layout.size (parent index)
          rw [upHeap_priorities heap layout index valid.verticesPositions valid.verticesKeys valid.positionsKeys]
          exact invariant.exchange_parent positive bound (by unfold parent; omega)
        · intro ref notVertices notPositions position
          rw [unchanged ref notVertices notPositions position]
          exact upHeap_read_other heap layout index ref position notVertices notPositions
        · intro vertex
          rw [presentIff vertex]
          exact swap_preserves_membership (heap.tick "heap_comparisons") layout index
            (Int.fdiv (index - 1) 2) valid.verticesPositions indexed nonnegative bound
            parentFacts.1 (by omega) vertex
        · intro name notComparisons notSwaps
          rw [otherClocks name notComparisons notSwaps]
          simp [nextHeap, upHeap, swapHeap, Heap.tick, Heap.write, notComparisons, notSwaps]
        · exact (show OtherStoragePreserved heap nextHeap from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage
    · refine ⟨heap, ?_, valid, indexed, Nat.le_add_right _ _, Nat.le_add_right _ _,
        ?_, ?_, ?_, ?_, OtherStoragePreserved.refl heap⟩
      · intro state location sameHeap
        simpa [sameHeap] using sift_up_stop state queue index location (by omega)
      · intro invariant
        exact invariant.finish (Or.inl (by omega))
      · intro ref _ _ position
        rfl
      · intro vertex
        rfl
      · intro name _ _
        rfl

-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.
























































-- Sift-down first selects the smaller child, then compares it with the parent.


























-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.


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
                    BinaryModuleAnalysis.AtSiftUp state queue index →
                      Eq.{1} (Algo2LeanCore.Config.heap.{0, 0, 0} state) heap →
                        Algo.indexed_heap.MinHeap.sift_up.CallFrom state after ()) ∧
                  layout.Valid after queue ∧
                    BinaryModuleAnalysis.Indexed (after.read layout.vertices)
                        (after.read layout.positions) layout.size ∧
                      LE.le.{0} (after.clocks "heap_comparisons")
                          (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_comparisons")
                            (BinaryModuleAnalysis.depth index)) ∧
                        LE.le.{0} (after.clocks "heap_swaps")
                            (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_swaps")
                              (BinaryModuleAnalysis.depth index)) ∧
                          (BinaryModuleAnalysis.UpInvariant
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
  BinaryModuleAnalysis.sift_up_loop
