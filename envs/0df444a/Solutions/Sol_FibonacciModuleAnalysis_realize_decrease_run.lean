-- Prove2me | solution 1 for FibonacciModuleAnalysis.realize_decrease_run
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:58.240934+00:00
-- url     : https://prove2.me/submissions/0a89d380-41b4-4b80-ad94-41d1e0bbe08c

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_decrease_effect_summary
import Theorems.Thm_FibonacciModuleAnalysis_realize_cascade_run


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



/-- An existing handle receiving no better key keeps all storage unchanged. -/
theorem push_unchanged_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int)
    (present : heap.read layout.present vertex ≠ 0)
    (noBetter : heap.read layout.keys vertex ≤ key) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key)
      ((heap.tick "heap_operations").tick "heap_comparisons") () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_false _ _ _
    (by simpa [valid.readPresent] using present))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc26 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc25_true _ _ _
    (by simpa [valid.readKeys] using noBetter))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc24 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc23 _ _ _)











































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis









































theorem lower_key_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    layout.Valid (lowerKeyHeap heap layout vertex key) queue := by
  apply Layout.Valid.write
  apply Layout.Valid.tick
  apply Layout.Valid.tick
  exact valid



theorem finish_decrease_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (finishDecreaseLayout heap layout vertex).Valid (finishDecreaseHeap heap queue layout vertex) queue := by
  unfold finishDecreaseHeap finishDecreaseLayout
  split
  · apply Layout.Valid.set_minimum
    exact Layout.Valid.tick _ _ _ valid _ _
  · exact Layout.Valid.tick _ _ _ valid _ _



-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.









theorem add_root_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (clock : String) :
    (addRootHeap heap queue layout vertex).clocks clock = heap.clocks clock +
      Clocks.single "heap_comparisons" (if layout.minimum < 0 then 0 else 1) clock := by
  unfold addRootHeap
  split
  · simp_all [rootHeaderHeap, set_FibonacciHeap_minimum, Clocks.single]
  · dsimp only
    split <;> by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [rootHeaderHeap, insertRingHeap, set_FibonacciHeap_minimum, Clocks.single]

/-- A cut changes only two clocks; the root insertion needs at most one comparison. -/
theorem cut_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) (clock : String) :
    (cutHeap heap queue layout vertex parent).clocks clock = heap.clocks clock +
      Clocks.single "heap_cuts" 1 clock +
      Clocks.single "heap_comparisons" (if layout.minimum < 0 then 0 else 1) clock := by
  have header : (cutHeaderHeap heap layout vertex parent).clocks clock = heap.clocks clock := by
    unfold cutHeaderHeap
    split <;> rfl
  unfold cutHeap cutTailHeap
  dsimp only
  simp only [Heap.tick]
  rw [add_root_clocks]
  by_cases cut : clock = "heap_cuts" <;>
    simp_all [removeHeap, Clocks.single, Nat.add_comm]

/-- Cascades perform exactly their recorded cuts, at most that many comparisons,
    and leave every other clock unchanged. -/
theorem CascadeEffect.clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  induction effect with
  | root => exact ⟨0, by omega, by intro clock; simp [Clocks.single]⟩
  | mark => exact ⟨0, by omega, by intro clock; simp [Clocks.single]⟩
  | @cut before after current final node count nonroot marked rest ih =>
    obtain ⟨comparisons, bounded, equation⟩ := ih
    refine ⟨comparisons + (if current.minimum < 0 then 0 else 1), ?_, ?_⟩
    · split <;> omega
    · intro clock
      rw [equation, cut_clocks]
      by_cases cut : clock = "heap_cuts" <;> by_cases cmp : clock = "heap_comparisons" <;>
        simp_all [Clocks.single] <;> omega











theorem finish_decrease_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (clock : String) :
    (finishDecreaseHeap heap queue layout vertex).clocks clock =
      heap.clocks clock + Clocks.single "heap_comparisons" 1 clock := by
  unfold finishDecreaseHeap
  split <;> by_cases same : clock = "heap_comparisons" <;>
    simp_all [set_FibonacciHeap_minimum, Clocks.single]

/-- Full decrease has constant overhead plus one cut and at most one comparison
    for each removed parent edge. -/
theorem DecreaseEffect.clocks {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts + 2 ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_cuts" cuts clock +
        Clocks.single "heap_comparisons" comparisons clock := by
  cases effect with
  | root =>
    refine ⟨1, by omega, ?_⟩
    intro clock
    simp [finish_decrease_clocks, Clocks.single]
  | ordered =>
    refine ⟨2, by omega, ?_⟩
    intro clock
    rw [finish_decrease_clocks]
    by_cases same : clock = "heap_comparisons" <;> simp_all [Clocks.single] <;> omega
  | @cut middle _ middleLayout count nonroot unordered cascade =>
    obtain ⟨comparisons, bounded, equation⟩ := cascade.clocks
    refine ⟨comparisons + (if layout.minimum < 0 then 0 else 1) + 2, ?_, ?_⟩
    · split <;> omega
    · intro clock
      rw [finish_decrease_clocks, equation, cut_clocks]
      by_cases cut : clock = "heap_cuts" <;> by_cases cmp : clock = "heap_comparisons" <;>
        simp_all [Clocks.single] <;> omega




























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

/-- Removing a ring node touches only this queue's declared storage. -/
theorem remove_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (removeHeap heap layout vertex) layout.refs [queue] := by
  unfold removeHeap
  repeat' apply Heap.Modifies.write
  all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

theorem add_root_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (addRootHeap heap queue layout vertex) layout.refs [queue] := by
  unfold addRootHeap
  dsimp only
  split
  · simp only [set_FibonacciHeap_minimum, rootHeaderHeap]
    repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]
  · split <;> simp only [set_FibonacciHeap_minimum, insertRingHeap, rootHeaderHeap]
    all_goals repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField | apply Heap.Modifies.tick
    all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

















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







/-- The public operation's initial key update has no other observable effect. -/
theorem lower_key_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    snapshot (lowerKeyHeap heap layout vertex key) layout =
      (snapshot heap layout).lowerKey vertex key := by
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
  all_goals simp [snapshot, lowerKeyHeap, Heap.read, Heap.write, Heap.tick,
    Algo2Lean.Fibonacci.Snapshot.lowerKey, Algo2Lean.Fibonacci.Rings.write,
    Ne.symm keys_parents, Ne.symm keys_children, Ne.symm keys_left, Ne.symm keys_right,
    Ne.symm keys_degrees, Ne.symm keys_marks, Ne.symm keys_present, Ne.symm keys_table]

/-- The final comparison changes only the minimum pointer. -/
theorem finish_decrease_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) :
    snapshot (finishDecreaseHeap heap queue layout vertex) (finishDecreaseLayout heap layout vertex) =
      (snapshot heap layout).finishDecrease vertex := by
  unfold finishDecreaseHeap finishDecreaseLayout
  dsimp only
  split <;> apply snapshot_ext
  all_goals try funext index
  all_goals simp_all [snapshot, Algo2Lean.Fibonacci.Snapshot.finishDecrease,
    set_FibonacciHeap_minimum, Heap.writeField, Heap.read, Heap.tick] <;> omega

end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated

/-- Cutting and repairing parent links stays inside the queue's footprint. -/
theorem cut_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex parent : Int) : heap.Modifies (cutHeap heap queue layout vertex parent) layout.refs [queue] := by
  have header : heap.Modifies (cutHeaderHeap heap layout vertex parent) layout.refs [queue] := by
    unfold cutHeaderHeap
    split
    · exact (Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs])
    · exact .refl _ _ _
  have decreased := header.write layout.degrees parent
    ((cutHeaderHeap heap layout vertex parent).read layout.degrees parent - 1) (by simp [Layout.refs])
  exact ((decreased.trans (remove_frame _ queue layout vertex)).trans
    (add_root_frame _ queue layout vertex)).tick "heap_cuts"

theorem CascadeEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | root => exact ⟨.refl _ _ _, rfl⟩
  | mark => exact ⟨(Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs]), rfl⟩
  | cut nonroot marked rest ih =>
    rw [cut_layout_refs] at ih
    exact ⟨(cut_frame _ _ _ _ _).trans ih.1, ih.2⟩

theorem finish_decrease_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) : heap.Modifies (finishDecreaseHeap heap queue layout vertex) layout.refs [queue] := by
  unfold finishDecreaseHeap
  dsimp only
  split
  · exact ((Heap.Modifies.refl _ _ _).tick "heap_comparisons").writeField queue "minimum" (.intValue vertex) (by simp)
  · exact (Heap.Modifies.refl _ _ _).tick "heap_comparisons"

theorem DecreaseEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex key : Int} {cuts : Nat}
    (effect : DecreaseEffect queue vertex key heap layout after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  cases effect with
  | root => exact ⟨finish_decrease_frame _ _ _ _, finish_decrease_layout_refs _ _ _⟩
  | ordered => exact ⟨((Heap.Modifies.refl _ _ _).tick "heap_comparisons").trans
      (finish_decrease_frame _ _ _ _), finish_decrease_layout_refs _ _ _⟩
  | @cut middle _ middleLayout count nonroot unordered cascade =>
    have framed := cascade.frame
    rw [cut_layout_refs] at framed
    have finished := finish_decrease_frame middle queue middleLayout vertex
    rw [framed.2] at finished
    exact ⟨(((Heap.Modifies.refl _ _ _).tick "heap_comparisons").trans (cut_frame _ _ _ _ _)).trans
      (framed.1.trans finished), (finish_decrease_layout_refs _ _ _).trans framed.2⟩

theorem push_decrease_frame (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  have preparation := (((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_operations").tick
    "heap_comparisons").write layout.keys vertex key (by simp [Layout.refs])
  exact ⟨preparation.trans effect.frame.1, effect.frame.2⟩



end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis
open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.fibonacci_heap Algo.fibonacci_heap.Algo2LeanGenerated





theorem push_decrease_clocks (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex key : Int) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    ∃ comparisons, comparisons ≤ cuts + 3 ∧ ∀ clock,
      after.clocks clock = heap.clocks clock + Clocks.single "heap_operations" 1 clock +
        Clocks.single "heap_cuts" cuts clock + Clocks.single "heap_comparisons" comparisons clock := by
  obtain ⟨comparisons, bounded, equation⟩ := effect.clocks
  refine ⟨comparisons + 1, by omega, ?_⟩
  intro clock
  rw [equation]
  by_cases op : clock = "heap_operations" <;> by_cases cut : clock = "heap_cuts" <;>
    by_cases cmp : clock = "heap_comparisons" <;>
      simp_all [lowerKeyHeap, Clocks.single] <;> omega









private theorem decrease_contract (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue)
    (vertex key : Int) (present : heap.read layout.present vertex ≠ 0)
    (smaller : key < heap.read layout.keys vertex) (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) (ready : finalLayout.Valid after queue) :
    UpdateContract heap after queue layout finalLayout vertex key cuts :=
  ⟨decrease_effect_summary heap after queue layout finalLayout valid vertex key present smaller cuts effect,
    ready, (push_decrease_frame heap after queue layout finalLayout vertex key cuts effect).1,
    (push_decrease_frame heap after queue layout finalLayout vertex key cuts effect).2,
    push_decrease_clocks heap after queue layout finalLayout vertex key cuts effect⟩

/-- Each forest-level decrease executes the compiled method with exactly the
    same snapshot and cuts. No caller transition or transcript is inspected. -/
theorem realize_decrease_run (before after : Algo2Lean.Fibonacci.Snapshot) (vertex key : Int) (cuts : Nat)
    (execution : Algo2Lean.Fibonacci.DecreaseRun before after vertex key cuts)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before)
    (present : heap.read layout.present vertex ≠ 0) :
    ∃ finalHeap finalLayout,
      UpdateContract heap finalHeap queue layout finalLayout vertex key cuts ∧
      snapshot finalHeap finalLayout = after := by
  cases execution with
  | unchanged noDecrease =>
    have noBetter : heap.read layout.keys vertex ≤ key := by
      change (snapshot heap layout).keys vertex ≤ key
      rw [observed]
      exact noDecrease
    refine ⟨(heap.tick "heap_operations").tick "heap_comparisons", layout, ?_, observed⟩
    refine ⟨push_unchanged_summary heap queue layout valid vertex key present noBetter,
      Layout.Valid.tick _ _ _ (Layout.Valid.tick _ _ _ valid _ _) _ _,
      ((Heap.Modifies.refl _ _ _).tick "heap_operations").tick "heap_comparisons", rfl, 1, by omega, ?_⟩
    intro clock
    by_cases operation : clock = "heap_operations" <;> by_cases comparison : clock = "heap_comparisons" <;>
      simp_all [Heap.tick, Clocks.single] <;> omega
  | root decreased root =>
    let prepared := lowerKeyHeap heap layout vertex key
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have noParent : prepared.read layout.parents vertex < 0 := by
      change (snapshot prepared layout).parents vertex < 0
      rw [prepareSnapshot]
      exact root
    refine ⟨finishDecreaseHeap prepared queue layout vertex, finishDecreaseLayout prepared layout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller 0 (.root _ _ noParent)
        (finish_decrease_layout _ _ _ prepareValid _), ?_⟩
    rw [finish_decrease_snapshot, prepareSnapshot]
  | ordered decreased nonroot ordered =>
    let prepared := lowerKeyHeap heap layout vertex key
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have hasParent : 0 ≤ prepared.read layout.parents vertex := by
      change 0 ≤ (snapshot prepared layout).parents vertex
      rw [prepareSnapshot]
      exact nonroot
    have parentKey : prepared.read layout.keys (prepared.read layout.parents vertex) ≤ key := by
      change (snapshot prepared layout).keys ((snapshot prepared layout).parents vertex) ≤ key
      rw [prepareSnapshot]
      exact ordered
    refine ⟨finishDecreaseHeap (prepared.tick "heap_comparisons") queue layout vertex,
      finishDecreaseLayout (prepared.tick "heap_comparisons") layout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller 0 (.ordered _ _ hasParent parentKey)
        (finish_decrease_layout _ _ _ (Layout.Valid.tick _ _ _ prepareValid _ _) _), ?_⟩
    rw [finish_decrease_snapshot, snapshot_tick, prepareSnapshot]
  | cascading decreased nonroot violates cascade =>
    rename_i middle count
    let prepared := lowerKeyHeap heap layout vertex key
    let compared := prepared.tick "heap_comparisons"
    have prepareValid : layout.Valid prepared queue := lower_key_layout heap queue layout valid vertex key
    have compareValid : layout.Valid compared queue := Layout.Valid.tick _ _ _ prepareValid _ _
    have prepareSnapshot : snapshot prepared layout = before.lowerKey vertex key :=
      (lower_key_snapshot heap queue layout valid vertex key).trans (congrArg (fun state => state.lowerKey vertex key) observed)
    have smaller : key < heap.read layout.keys vertex := by
      change key < (snapshot heap layout).keys vertex
      rw [observed]
      exact decreased
    have hasParent : 0 ≤ prepared.read layout.parents vertex := by
      change 0 ≤ (snapshot prepared layout).parents vertex
      rw [prepareSnapshot]
      exact nonroot
    have parentRead : prepared.read layout.parents vertex = before.parents vertex :=
      congrArg (fun state => state.parents vertex) prepareSnapshot
    have parentKey : key < prepared.read layout.keys (prepared.read layout.parents vertex) := by
      change key < (snapshot prepared layout).keys ((snapshot prepared layout).parents vertex)
      rw [prepareSnapshot]
      exact violates
    have cutObserved : snapshot (cutHeap compared queue layout vertex (prepared.read layout.parents vertex))
        (cutLayout compared layout vertex (prepared.read layout.parents vertex)) =
          (before.lowerKey vertex key).cut vertex (before.parents vertex) := by
      rw [cut_snapshot compared queue layout compareValid, snapshot_tick, prepareSnapshot, parentRead]
    obtain ⟨finalHeap, finalLayout, effect, ready, result⟩ := realize_cascade_run _ _ _ count cascade
      (cutHeap compared queue layout vertex (prepared.read layout.parents vertex)) queue
      (cutLayout compared layout vertex (prepared.read layout.parents vertex))
      (cut_layout compared queue layout compareValid vertex _) cutObserved
    have cascadeEffect : CascadeEffect queue
        (cutHeap compared queue layout vertex (prepared.read layout.parents vertex))
        (cutLayout compared layout vertex (prepared.read layout.parents vertex))
        (prepared.read layout.parents vertex) finalHeap finalLayout count := by
      simpa only [parentRead] using effect
    refine ⟨finishDecreaseHeap finalHeap queue finalLayout vertex,
      finishDecreaseLayout finalHeap finalLayout vertex,
      decrease_contract heap _ queue layout _ valid vertex key present smaller (count + 1)
        (.cut hasParent parentKey cascadeEffect) (finish_decrease_layout _ _ _ ready _), ?_⟩
    rw [finish_decrease_snapshot, result]



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
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (vertex key : Int) (cuts : Nat),
      Algo2Lean.Fibonacci.DecreaseRun before after vertex key cuts →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Ne.{1} (heap.read layout.present vertex) (0 : Int) →
                Exists.{1} fun finalHeap =>
                  Exists.{1} fun finalLayout =>
                    FibonacciModuleAnalysis.UpdateContract heap finalHeap queue layout finalLayout
                        vertex key cuts ∧
                      Eq.{1} (FibonacciModuleAnalysis.snapshot finalHeap finalLayout) after :=
  FibonacciModuleAnalysis.realize_decrease_run
