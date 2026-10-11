-- Prove2me | solution 1 for BinaryModuleAnalysis.insert_correct
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:10.733895+00:00
-- url     : https://prove2.me/submissions/fc97a3a3-2d35-49e6-8ccc-5a28f83ecebc

import Definitions.Def_Algo_indexed_heap_Analysis
import Theorems.Thm_BinaryModuleAnalysis_sift_up_loop


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




-- A permutation of positions, with all other positions left fixed.










-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.








-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.


-- Position numbers may change, but exactly the same vertices remain present.






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
























/-- Appending an absent vertex updates both directions of the position map. -/
theorem Indexed.insert {vertices positions : Seq} {size vertex : Int}
    (indexed : Indexed vertices positions size) (nonnegative : 0 ≤ size)
    (absent : positions vertex = -1) :
    Indexed (fun index => if index = size then vertex else vertices index)
      (fun value => if value = vertex then size else positions value) (size + 1) := by
  constructor
  · intro index lower upper
    by_cases last : index = size
    · subst index; simp
    · have oldBound : index < size := by omega
      have different : vertices index ≠ vertex := by
        intro same
        have old := indexed.forward index lower oldBound
        rw [same, absent] at old
        omega
      simpa [last, different] using indexed.forward index lower oldBound
  · intro value present
    by_cases same : value = vertex
    · subst value; simp; omega
    · simp only [same, ite_false] at present ⊢
      obtain ⟨bound, identity⟩ := indexed.backward value present
      have different : positions value ≠ size := by omega
      exact ⟨by omega, by simp [different, identity]⟩
  · intro value negative
    by_cases same : value = vertex
    · subst value
      simp only [ite_true] at negative
      omega
    · simpa [same] using indexed.absent value (by simpa [same] using negative)

/-- Adding a leaf preserves all order edges except the new leaf's parent edge. -/
theorem Ordered.append {priority : Seq} {size key : Int}
    (ordered : Ordered priority size) :
    UpInvariant (fun index => if index = size then key else priority index) (size + 1) size := by
  constructor
  · intro child positive bound different
    have oldBound : child < size := by omega
    have parentBound : parent child < child := (parent_bounds child positive).2
    have parentDifferent : parent child ≠ size := by omega
    simpa [different, parentDifferent] using ordered child positive oldBound
  · intro child positive bound fromLast lastPositive
    have parentBound : parent child < child := (parent_bounds child positive).2
    omega

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
theorem sift_up_summary (heap : Heap) (queue : Ref_MinHeap) (layout : Layout) (index : Int)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ index) (bound : index < layout.size) :
    ∃ after, MinHeap.sift_up.Call heap (queue, index) after () ∧
      layout.Valid after queue ∧
      Indexed (after.read layout.vertices) (after.read layout.positions) layout.size ∧
      Heap.cost heap after "heap_comparisons" ≤ depth index ∧
      Heap.cost heap after "heap_swaps" ≤ depth index ∧
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
  obtain ⟨after, remaining, afterValid, afterIndexed, comparisons, swaps, repair,
      unchanged, presentIff, otherClocks, storage⟩ :=
    sift_up_loop heap queue layout index valid indexed nonnegative bound
  refine ⟨after, ⟨valid.object, ?_⟩, afterValid, afterIndexed, ?_, ?_, repair,
    unchanged, presentIff, otherClocks, storage⟩
  · exact remaining (MinHeap.sift_up.initial heap (queue, index)) ⟨True.intro, rfl, rfl⟩ rfl
  · unfold Heap.cost
    omega
  · unfold Heap.cost
    omega









/-- Insertion itself is a few writes, followed by a reusable sift-up summary. -/
theorem append_summary (heap finalHeap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (absent : heap.read layout.positions vertex < 0)
    (sift : MinHeap.sift_up.Call (appendedHeap heap queue layout vertex key)
      (queue, layout.size) finalHeap ()) :
    MinHeap.push_or_decrease.Call heap (queue, vertex, key) finalHeap () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc25 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc24 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc23_true _ _ _
    (by simp [valid.readPositions, absent]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc14 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc13 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc12 _ _ _
    (by simp [valid.readVertices, valid.verticesAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc11 _ _ _
    (by simp [valid.readPositions, valid.positionsAllocated]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc9 _ _ _
    (by simp [valid.readSize]))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc8 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc7 _ _ _ valid.object)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc5 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_size] using! valid.object))
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc3 _ _ _)
  simp only [vertices_write, positions_write, size_write,
    valid.readVertices, valid.readPositions, valid.readKeys, valid.readSize,
    Option.getD_some]
  apply Reaches.trans (sift.2 _)
  apply Reaches.prepend (Step.MinHeap_push_or_decrease_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_push_or_decrease_pc1 _ _ _)



theorem appended_layout (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    { layout with size := layout.size + 1 }.Valid (appendedHeap heap queue layout vertex key) queue := by
  constructor
  · simpa [appendedHeap, is_MinHeap, set_MinHeap_size] using! valid.object
  · simpa [appendedHeap, field_MinHeap_vertices, is_MinHeap, set_MinHeap_size] using! valid.readVertices
  · simpa [appendedHeap, field_MinHeap_positions, is_MinHeap, set_MinHeap_size] using! valid.readPositions
  · simpa [appendedHeap, field_MinHeap_keys, is_MinHeap, set_MinHeap_size] using! valid.readKeys
  · exact field_MinHeap_size_set _ _ _ valid.object
  · exact valid.verticesAllocated
  · exact valid.positionsAllocated
  · exact valid.keysAllocated
  · exact valid.verticesPositions
  · exact valid.verticesKeys
  · exact valid.positionsKeys

theorem appended_vertices (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key index : Int) :
    (appendedHeap heap queue layout vertex key).read layout.vertices index =
      if index = layout.size then vertex else heap.read layout.vertices index := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    valid.verticesPositions, valid.verticesKeys]

theorem appended_positions (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.positions value =
      if value = vertex then layout.size else heap.read layout.positions value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesPositions, valid.positionsKeys]

theorem appended_keys (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key value : Int) :
    (appendedHeap heap queue layout vertex key).read layout.keys value =
      if value = vertex then key else heap.read layout.keys value := by
  simp [appendedHeap, set_MinHeap_size, Heap.read, Heap.write,
    Ne.symm valid.verticesKeys, Ne.symm valid.positionsKeys]

theorem appended_indexed (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (nonnegative : 0 ≤ layout.size) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    Indexed ((appendedHeap heap queue layout vertex key).read layout.vertices)
      ((appendedHeap heap queue layout vertex key).read layout.positions) (layout.size + 1) := by
  have vertices : (appendedHeap heap queue layout vertex key).read layout.vertices =
      (fun index => if index = layout.size then vertex else heap.read layout.vertices index) :=
    funext (appended_vertices heap queue layout valid vertex key)
  have positions : (appendedHeap heap queue layout vertex key).read layout.positions =
      (fun value => if value = vertex then layout.size else heap.read layout.positions value) :=
    funext (appended_positions heap queue layout valid vertex key)
  rw [vertices, positions]
  exact indexed.insert nonnegative absent



theorem UpInvariant.congr {first second : Seq} {size index : Int}
    (invariant : UpInvariant first size index)
    (within : index < size)
    (same : ∀ position, 0 ≤ position → position < size → first position = second position) :
    UpInvariant second size index := by
  constructor
  · intro child positive bound different
    have bounds : 0 ≤ parent child ∧ parent child < child := parent_bounds child positive
    rw [← same child (by omega) bound, ← same (parent child) bounds.1 (by omega)]
    exact invariant.orderedExcept child positive bound different
  · intro child positive bound fromIndex indexPositive
    have bounds : 0 ≤ parent index ∧ parent index < index := parent_bounds index indexPositive
    rw [← same child (by omega) bound, ← same (parent index) bounds.1 (by omega)]
    exact invariant.parentBelowChildren child positive bound fromIndex indexPositive

/-- Appending an absent vertex creates exactly the local disorder that sift-up repairs. -/
theorem appended_order (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (valid : layout.Valid heap queue)
    (indexed : Indexed (heap.read layout.vertices) (heap.read layout.positions) layout.size)
    (ordered : Ordered (fun index => heap.read layout.keys (heap.read layout.vertices index)) layout.size)
    (vertex key : Int) (absent : heap.read layout.positions vertex = -1) :
    UpInvariant (fun index => (appendedHeap heap queue layout vertex key).read layout.keys
      ((appendedHeap heap queue layout vertex key).read layout.vertices index)) (layout.size + 1) layout.size := by
  apply (ordered.append (key := key)).congr (by omega)
  intro index lower upper
  rw [appended_keys heap queue layout valid, appended_vertices heap queue layout valid]
  by_cases last : index = layout.size
  · simp [last]
  · have oldBound : index < layout.size := by omega
    have different : heap.read layout.vertices index ≠ vertex := by
      intro same
      have old := indexed.forward index lower oldBound
      rw [same, absent] at old
      omega
    simp [last, different]









/-- Insert one absent vertex, restore heap order, and pay at most one comparison
    and swap per parent level. No other vertex enters or leaves the queue. -/
theorem insert_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (vertex key : Int)
    (absent : heap.read layout.positions vertex = -1) :
    ∃ after, MinHeap.push_or_decrease.Call heap (queue, vertex, key) after () ∧
      QueueRep after queue { layout with size := layout.size + 1 } ∧
      (∀ value, 0 ≤ after.read layout.positions value ↔
        value = vertex ∨ 0 ≤ heap.read layout.positions value) ∧
      (∀ value, after.read layout.keys value =
        if value = vertex then key else heap.read layout.keys value) ∧
      Heap.cost heap after "heap_comparisons" ≤ depth layout.size ∧
      Heap.cost heap after "heap_swaps" ≤ depth layout.size ∧
      (∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
        ∀ index, after.read ref index = heap.read ref index) ∧
      (∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
        after.clocks name = heap.clocks name) ∧
      OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) after := by
  have sizeNonnegative := representation.nonnegative
  let prepared := appendedHeap heap queue layout vertex key
  let enlarged := { layout with size := layout.size + 1 }
  have valid : enlarged.Valid prepared queue :=
    appended_layout heap queue layout representation.valid vertex key
  have indexed : Indexed (prepared.read layout.vertices) (prepared.read layout.positions) enlarged.size :=
    appended_indexed heap queue layout representation.valid representation.indexed
      representation.nonnegative vertex key absent
  obtain ⟨after, sift, afterValid, afterIndexed, comparisons, swaps, repair, unchanged, membership, clocks, storage⟩ :=
    sift_up_summary prepared queue enlarged layout.size valid indexed representation.nonnegative (by dsimp [enlarged]; omega)
  refine ⟨after, append_summary heap after queue layout representation.valid vertex key (by omega) sift,
    ⟨afterValid, by dsimp [enlarged]; omega, afterIndexed, ?_⟩, ?_, ?_, comparisons, swaps, ?_, ?_, ?_⟩
  · exact repair (appended_order heap queue layout representation.valid representation.indexed
      representation.ordered vertex key absent)
  · intro value
    rw [membership value]
    change 0 ≤ (appendedHeap heap queue layout vertex key).read layout.positions value ↔ _
    rw [appended_positions heap queue layout representation.valid]
    by_cases same : value = vertex <;> simp [same, representation.nonnegative]
  · intro value
    rw [unchanged layout.keys (Ne.symm representation.valid.verticesKeys)
      (Ne.symm representation.valid.positionsKeys) value]
    exact appended_keys heap queue layout representation.valid vertex key value
  · intro ref notVertices notPositions notKeys index
    rw [unchanged ref notVertices notPositions index]
    simp [prepared, appendedHeap, set_MinHeap_size, Heap.read, Heap.write, notVertices, notPositions, notKeys]
  · exact clocks
  · exact (show OtherStoragePreserved (set_MinHeap_size heap queue (layout.size + 1)) prepared
      from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans storage

















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
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        ∀ (vertex key : Int),
          Eq.{1} (heap.read layout.positions vertex) (-1 : Int) →
            Exists.{1} fun after =>
              Algo.indexed_heap.MinHeap.push_or_decrease.Call heap
                  (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () ∧
                BinaryModuleAnalysis.QueueRep after queue
                    { vertices := layout.vertices, positions := layout.positions, keys := layout.keys,
                      size := HAdd.hAdd.{0, 0, 0} layout.size (1 : Int) } ∧
                  (∀ (value : Int),
                      LE.le.{0} (0 : Int) (after.read layout.positions value) ↔
                        Eq.{1} value vertex ∨ LE.le.{0} (0 : Int) (heap.read layout.positions value)) ∧
                    (∀ (value : Int),
                        Eq.{1} (after.read layout.keys value)
                          (ite.{1} (Eq.{1} value vertex) key (heap.read layout.keys value))) ∧
                      LE.le.{0} (heap.cost after "heap_comparisons")
                          (BinaryModuleAnalysis.depth layout.size) ∧
                        LE.le.{0} (heap.cost after "heap_swaps")
                            (BinaryModuleAnalysis.depth layout.size) ∧
                          (∀ (ref : Algo2LeanGenerated.SeqRef),
                              Ne.{1} ref layout.vertices →
                                Ne.{1} ref layout.positions →
                                  Ne.{1} ref layout.keys →
                                    ∀ (index : Int),
                                      Eq.{1} (after.read ref index) (heap.read ref index)) ∧
                            (∀ (name : String),
                                Ne.{1} name "heap_comparisons" →
                                  Ne.{1} name "heap_swaps" →
                                    Eq.{1} (after.clocks name) (heap.clocks name)) ∧
                              BinaryModuleAnalysis.OtherStoragePreserved
                                (Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_size heap queue
                                  (HAdd.hAdd.{0, 0, 0} layout.size (1 : Int)))
                                after :=
  BinaryModuleAnalysis.insert_correct
