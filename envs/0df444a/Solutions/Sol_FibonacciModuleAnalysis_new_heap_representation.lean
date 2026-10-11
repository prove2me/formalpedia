-- Prove2me | solution 1 for FibonacciModuleAnalysis.new_heap_representation
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:27.289728+00:00
-- url     : https://prove2.me/submissions/7bfd6e36-1e2b-4f80-9500-8b03e20bd631

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The representation boundary between Fibonacci forests and mutable indexed storage.
Snapshots contain ordinary array observations, not a compiler configuration or a
transcript. A compiled operation must establish preservation of this relation.
-/

namespace Algo2Lean.Fibonacci



























/-- The constructor's observable empty state establishes the invariant without
    any assumptions about unused sequence cells or pre-existing client data. -/
theorem Represented.empty (state : Snapshot)
    (absent : ∀ vertex, state.present vertex = 0)
    (emptySize : state.size = 0) (emptyMinimum : state.minimum = -1)
    (table : ∀ degree, state.table degree = -1) : Represented state [] := by
  refine ⟨?_, Or.inl rfl, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, emptyMinimum⟩, fun degree => by rw [table degree]; omega⟩
  · simp [Forest.Valid, Forest.Unique, Forest.entries, Forest.Ordered,
      Forest.Ranked, Forest.RootsUnmarked]
  · simp
  · simp [Forest.entries]
  · simp [absent, Forest.entries]
  · simpa [Forest.entries] using emptySize































































































































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_representation`: Empty Fibonacci heap representation.
- `QueueRep.update`: Insertion and decrease-key amortized contract.
- `QueueRep.pop_minimum`: Minimum extraction amortized contract.
-/

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

namespace FibonacciModuleAnalysis

-- Storage descriptions are independent of the mathematical forest invariant.
-- This lets local ring facts apply inside any caller and at any named location.




























-- Detaching a vertex changes four links and does not require a whole run.












-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.




theorem initialized_object (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    is_FibonacciHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_FibonacciHeap, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size] using valid







theorem initialization_layout (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    (emptyLayout heap).Valid (initializedHeap heap queue) queue := by
  constructor
  · exact initialized_object heap queue valid
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_keys, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_parents, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_children, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_left, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_right, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_degrees, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_marks, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_present, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_table, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_minimum, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asInt, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_FibonacciHeap_size, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size,
      is_FibonacciHeap, valid.1, valid.2, ObjectValue.asInt, Nat.add_assoc]
  · change heap.nextRef < heap.nextRef + 9
    omega
  · change heap.nextRef + 1 < heap.nextRef + 9
    omega
  · change heap.nextRef + 2 < heap.nextRef + 9
    omega
  · change heap.nextRef + 3 < heap.nextRef + 9
    omega
  · change heap.nextRef + 4 < heap.nextRef + 9
    omega
  · change heap.nextRef + 5 < heap.nextRef + 9
    omega
  · change heap.nextRef + 6 < heap.nextRef + 9
    omega
  · change heap.nextRef + 7 < heap.nextRef + 9
    omega
  · change heap.nextRef + 8 < heap.nextRef + 9
    omega
  · simp [Layout.refs, emptyLayout]





theorem initialized_table (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).table vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]











theorem initialized_present (heap : Heap) (queue : Ref_FibonacciHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).present vertex = 0 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, Nat.add_assoc, set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children, set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees, set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table, set_FibonacciHeap_minimum, set_FibonacciHeap_size]

















































-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.















-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.




























-- Ranking every parent pointer is a strong sufficient termination premise.
-- The scoped parent-rank invariant restricts the ordering to active vertices, so unused
-- sequence cells can remain unconstrained. Cutting edges preserves either form.




-- A source-facing description of the cascade's exact heap changes. It records
-- actual cuts and marks, independently of the compiler's temporary states.






-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.






theorem initialization_representation (heap : Heap) (queue : Ref_FibonacciHeap)
    (valid : is_FibonacciHeap heap queue) :
    QueueRep (initializedHeap heap queue) queue (emptyLayout heap) [] := by
  refine ⟨initialization_layout heap queue valid, ?_⟩
  apply Algo2Lean.Fibonacci.Represented.empty
  · exact initialized_present heap queue
  · rfl
  · rfl
  · exact initialized_table heap queue

theorem new_heap_representation (heap : Heap) :
    QueueRep (newHeap heap) heap.nextObject (emptyLayout heap) [] := by
  exact initialization_representation (heap.allocateObject "fibonacci_heap.FibonacciHeap") heap.nextObject
    (by simp [is_FibonacciHeap])






end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis















































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

















































-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
























































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis





























end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings



































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis



















































































































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis






















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated













end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated





















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated









end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis



























end FibonacciModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap),
      FibonacciModuleAnalysis.QueueRep (FibonacciModuleAnalysis.newHeap heap) heap.nextObject
        (FibonacciModuleAnalysis.emptyLayout heap) List.nil.{0} :=
  FibonacciModuleAnalysis.new_heap_representation
