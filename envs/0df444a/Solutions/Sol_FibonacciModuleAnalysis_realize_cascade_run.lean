-- Prove2me | solution 1 for FibonacciModuleAnalysis.realize_cascade_run
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:35.082932+00:00
-- url     : https://prove2.me/submissions/b70dde8c-effa-4851-873e-65bb4b097dec

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis


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




theorem remove_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (removeHeap heap layout vertex) queue := by
  exact ⟨valid.object, valid.readKeys, valid.readParents, valid.readChildren, valid.readLeft, valid.readRight, valid.readDegrees, valid.readMarks, valid.readPresent, valid.readTable, valid.readMinimum, valid.readSize, valid.keysAllocated, valid.parentsAllocated, valid.childrenAllocated, valid.leftAllocated, valid.rightAllocated, valid.degreesAllocated, valid.marksAllocated, valid.presentAllocated, valid.tableAllocated, valid.separate⟩







-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.
















































































-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.















-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.


theorem Layout.Valid.set_minimum (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (minimum : Int) :
    { layout with minimum := minimum }.Valid (set_FibonacciHeap_minimum heap queue minimum) queue := by
  constructor
  · simpa [set_FibonacciHeap_minimum, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readTable
  · exact field_FibonacciHeap_minimum_set heap queue minimum valid.object
  · simpa [field_FibonacciHeap_size, set_FibonacciHeap_minimum, is_FibonacciHeap]
      using valid.readSize
  · exact valid.keysAllocated
  · exact valid.parentsAllocated
  · exact valid.childrenAllocated
  · exact valid.leftAllocated
  · exact valid.rightAllocated
  · exact valid.degreesAllocated
  · exact valid.marksAllocated
  · exact valid.presentAllocated
  · exact valid.tableAllocated
  · exact valid.separate



theorem add_root_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (addRootLayout heap layout vertex).Valid (addRootHeap heap queue layout vertex) queue := by
  unfold addRootHeap addRootLayout
  dsimp only
  split
  · apply Layout.Valid.set_minimum
    repeat apply Layout.Valid.write
    exact valid
  · split
    · apply Layout.Valid.set_minimum
      apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid
    · apply Layout.Valid.tick
      repeat apply Layout.Valid.write
      exact valid



theorem cut_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    layout.Valid (cutHeaderHeap heap layout vertex parent) queue := by
  unfold cutHeaderHeap
  split
  · exact Layout.Valid.write _ _ _ valid _ _ _
  · exact valid

theorem cut_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    (cutLayout heap layout vertex parent).Valid (cutHeap heap queue layout vertex parent) queue := by
  unfold cutHeap cutTailHeap cutLayout
  apply Layout.Valid.tick
  apply add_root_layout
  apply remove_preserves_layout
  apply Layout.Valid.write
  exact cut_header_layout heap queue layout valid vertex parent















-- Ranking every parent pointer is a strong sufficient termination premise.
-- The scoped parent-rank invariant restricts the ordering to active vertices, so unused
-- sequence cells can remain unconstrained. Cutting edges preserves either form.




-- A source-facing description of the cascade's exact heap changes. It records
-- actual cuts and marks, independently of the compiler's temporary states.






-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.















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






















































private theorem snapshot_ext (before after : Algo2Lean.Fibonacci.Snapshot)
    (keys : before.keys = after.keys) (parents : before.parents = after.parents)
    (children : before.children = after.children) (left : before.left = after.left)
    (right : before.right = after.right) (degrees : before.degrees = after.degrees)
    (marks : before.marks = after.marks) (present : before.present = after.present)
    (table : before.table = after.table) (minimum : before.minimum = after.minimum)
    (size : before.size = after.size) : before = after := by
  cases before
  cases after
  simp_all









































/-- Root insertion matches the forest-storage effect for any detached tree. -/
theorem add_root_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (addRootHeap heap queue layout vertex) (addRootLayout heap layout vertex) =
      (snapshot heap layout).addRoot vertex := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases empty : layout.minimum < 0
  · apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, set_FibonacciHeap_minimum, Heap.read,
      Heap.write, Heap.writeField, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, empty, keys_parents, keys_left, keys_right, keys_marks,
      parents_left, parents_right, parents_marks, children_left, children_right, children_marks,
      left_right, left_marks, right_marks, degrees_marks, Ne.symm parents_children, Ne.symm
      parents_left, Ne.symm parents_right, Ne.symm parents_degrees, Ne.symm parents_marks, Ne.symm
      parents_present, Ne.symm parents_table, Ne.symm left_right, Ne.symm left_degrees, Ne.symm
      left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm right_degrees, Ne.symm
      right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm marks_present, Ne.symm
      marks_table]
  · by_cases smaller : heap.read layout.keys vertex < heap.read layout.keys layout.minimum
    all_goals
      simp only [Heap.read] at smaller
      apply snapshot_ext
      all_goals try funext index
      all_goals simp [snapshot, addRootHeap, addRootLayout, rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum,
      Heap.read, Heap.write, Heap.writeField, Heap.tick, Algo2Lean.Fibonacci.Snapshot.addRoot,
      Algo2Lean.Fibonacci.Rings.write, Algo2Lean.Fibonacci.Rings.insertAfterLeft,
      Algo2Lean.Fibonacci.Rings.insertAfterRight, empty, smaller, keys_parents, keys_left,
      keys_right, keys_marks, parents_left, parents_right, parents_marks, children_left,
      children_right, children_marks, left_right, left_marks, right_marks, degrees_marks, Ne.symm
      parents_children, Ne.symm parents_left, Ne.symm parents_right, Ne.symm parents_degrees,
      Ne.symm parents_marks, Ne.symm parents_present, Ne.symm parents_table, Ne.symm left_right,
      Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm
      right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm
      marks_present, Ne.symm marks_table]


















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis






















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- The first part of a cut matches the pure child-removal effect. -/
theorem remove_child_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    let headed := cutHeaderHeap heap layout vertex parent
    let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
    snapshot (removeHeap decreased layout vertex) layout =
      (snapshot heap layout).removeChild vertex parent := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  by_cases first : heap.read layout.children parent = vertex
  all_goals
    simp only [Heap.read] at first
    apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, cutHeaderHeap, removeHeap, Heap.read, Heap.write,
      Algo2Lean.Fibonacci.Snapshot.removeChild, Algo2Lean.Fibonacci.Rings.removeLeft,
      Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write, first, keys_children, keys_left, keys_right, keys_degrees, parents_children, parents_left, parents_right, parents_degrees, children_left, children_right, children_degrees, left_right, left_degrees, right_degrees, Ne.symm children_left, Ne.symm children_right, Ne.symm children_degrees, Ne.symm children_marks, Ne.symm children_present, Ne.symm children_table, Ne.symm left_right, Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm left_table, Ne.symm right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm right_table, Ne.symm degrees_marks, Ne.symm degrees_present, Ne.symm degrees_table]
    all_goals rintro rfl; rfl

/-- The compiled cut and the pure pointer update have exactly the same snapshot. -/
theorem cut_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    snapshot (cutHeap heap queue layout vertex parent) (cutLayout heap layout vertex parent) =
      (snapshot heap layout).cut vertex parent := by
  unfold cutHeap cutTailHeap cutLayout
  simp only [snapshot_tick]
  let headed := cutHeaderHeap heap layout vertex parent
  let decreased := headed.write layout.degrees parent (headed.read layout.degrees parent - 1)
  have ready : layout.Valid (removeHeap decreased layout vertex) queue :=
    remove_preserves_layout _ _ _
      (Layout.Valid.write _ _ _ (cut_header_layout heap queue layout valid vertex parent) _ _ _) vertex
  rw [add_root_snapshot _ _ _ ready]
  rw [remove_child_snapshot heap queue layout valid vertex parent]
  rfl

/-- Mark changes are ordinary one-cell updates, independent of the call stack. -/
theorem mark_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (marked : Bool) :
    snapshot (heap.write layout.marks vertex (if marked then 1 else 0)) layout =
      (snapshot heap layout).setMark vertex marked := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys_parents : layout.keys ≠ layout.parents := different.1.1
  have keys_children : layout.keys ≠ layout.children := different.1.2.1
  have keys_left : layout.keys ≠ layout.left := different.1.2.2.1
  have keys_right : layout.keys ≠ layout.right := different.1.2.2.2.1
  have keys_degrees : layout.keys ≠ layout.degrees := different.1.2.2.2.2.1
  have keys_marks : layout.keys ≠ layout.marks := different.1.2.2.2.2.2.1
  have keys_present : layout.keys ≠ layout.present := different.1.2.2.2.2.2.2.1
  have keys_table : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents_children : layout.parents ≠ layout.children := different.2.1.1
  have parents_left : layout.parents ≠ layout.left := different.2.1.2.1
  have parents_right : layout.parents ≠ layout.right := different.2.1.2.2.1
  have parents_degrees : layout.parents ≠ layout.degrees := different.2.1.2.2.2.1
  have parents_marks : layout.parents ≠ layout.marks := different.2.1.2.2.2.2.1
  have parents_present : layout.parents ≠ layout.present := different.2.1.2.2.2.2.2.1
  have parents_table : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children_left : layout.children ≠ layout.left := different.2.2.1.1
  have children_right : layout.children ≠ layout.right := different.2.2.1.2.1
  have children_degrees : layout.children ≠ layout.degrees := different.2.2.1.2.2.1
  have children_marks : layout.children ≠ layout.marks := different.2.2.1.2.2.2.1
  have children_present : layout.children ≠ layout.present := different.2.2.1.2.2.2.2.1
  have children_table : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left_right : layout.left ≠ layout.right := different.2.2.2.1.1
  have left_degrees : layout.left ≠ layout.degrees := different.2.2.2.1.2.1
  have left_marks : layout.left ≠ layout.marks := different.2.2.2.1.2.2.1
  have left_present : layout.left ≠ layout.present := different.2.2.2.1.2.2.2.1
  have left_table : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right_degrees : layout.right ≠ layout.degrees := different.2.2.2.2.1.1
  have right_marks : layout.right ≠ layout.marks := different.2.2.2.2.1.2.1
  have right_present : layout.right ≠ layout.present := different.2.2.2.2.1.2.2.1
  have right_table : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees_marks : layout.degrees ≠ layout.marks := different.2.2.2.2.2.1.1
  have degrees_present : layout.degrees ≠ layout.present := different.2.2.2.2.2.1.2.1
  have degrees_table : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks_present : layout.marks ≠ layout.present := different.2.2.2.2.2.2.1.1
  have marks_table : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present_table : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, Heap.read, Heap.write,
    Algo2Lean.Fibonacci.Snapshot.setMark, Algo2Lean.Fibonacci.Rings.write, keys_marks, parents_marks, children_marks, left_marks, right_marks, degrees_marks, Ne.symm marks_present, Ne.symm marks_table]



/-- A forest-level cascade proof can be reused directly as a compiled call
    summary, preserving its final snapshot and exact number of cuts. -/
theorem realize_cascade_run (before after : Algo2Lean.Fibonacci.Snapshot) (vertex : Int) (cuts : Nat)
    (execution : Algo2Lean.Fibonacci.CascadeRun before after vertex cuts)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap finalLayout,
      CascadeEffect queue heap layout vertex finalHeap finalLayout cuts ∧
      finalLayout.Valid finalHeap queue ∧ snapshot finalHeap finalLayout = after := by
  induction execution generalizing heap layout with
  | @root state vertex root =>
    refine ⟨heap, layout, .root heap layout vertex ?_, valid, observed⟩
    change (snapshot heap layout).parents vertex < 0
    rw [observed]
    exact root
  | @mark state vertex nonroot unmarked =>
    have parent : 0 ≤ heap.read layout.parents vertex := by
      change 0 ≤ (snapshot heap layout).parents vertex
      rw [observed]
      exact nonroot
    have clear : heap.read layout.marks vertex = 0 := by
      change (snapshot heap layout).marks vertex = 0
      rw [observed]
      exact unmarked
    refine ⟨heap.write layout.marks vertex 1, layout, .mark heap layout vertex parent clear,
      Layout.Valid.write _ _ _ valid _ _ _, ?_⟩
    have markedSnapshot := mark_snapshot heap queue layout valid vertex true
    change snapshot (heap.write layout.marks vertex 1) layout =
      (snapshot heap layout).setMark vertex true at markedSnapshot
    rw [markedSnapshot, observed]
  | @cut state final vertex count nonroot marked next ih =>
    have parent : 0 ≤ heap.read layout.parents vertex := by
      change 0 ≤ (snapshot heap layout).parents vertex
      rw [observed]
      exact nonroot
    have marked' : heap.read layout.marks vertex ≠ 0 := by
      change (snapshot heap layout).marks vertex ≠ 0
      rw [observed]
      exact marked
    have parentRead : heap.read layout.parents vertex = state.parents vertex :=
      congrArg (fun state => state.parents vertex) observed
    have nextObserved :
        snapshot (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
          (cutLayout heap layout vertex (heap.read layout.parents vertex)) =
            state.cut vertex (state.parents vertex) := by
      rw [cut_snapshot heap queue layout valid, observed, parentRead]
    obtain ⟨finalHeap, finalLayout, effect, ready, result⟩ :=
      ih (cutHeap heap queue layout vertex (heap.read layout.parents vertex))
        (cutLayout heap layout vertex (heap.read layout.parents vertex))
        (cut_layout heap queue layout valid vertex _) nextObserved
    refine ⟨finalHeap, finalLayout, .cut parent marked' ?_, ready, result⟩
    simpa only [parentRead] using effect





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
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (vertex : Int) (cuts : Nat),
      Algo2Lean.Fibonacci.CascadeRun before after vertex cuts →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Exists.{1} fun finalHeap =>
                Exists.{1} fun finalLayout =>
                  FibonacciModuleAnalysis.CascadeEffect queue heap layout vertex finalHeap finalLayout
                      cuts ∧
                    finalLayout.Valid finalHeap queue ∧
                      Eq.{1} (FibonacciModuleAnalysis.snapshot finalHeap finalLayout) after :=
  FibonacciModuleAnalysis.realize_cascade_run
