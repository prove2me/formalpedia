-- Prove2me | solution 1 for FibonacciModuleAnalysis.realize_root_consumption
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:50.876388+00:00
-- url     : https://prove2.me/submissions/7bd7bb0e-99c1-4802-8379-354f5017411a

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_realize_bucket_collisions


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











































theorem detach_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) : (detachLayout heap layout).Valid (detachHeap heap queue layout) queue := by
  apply Layout.Valid.tick
  apply remove_preserves_layout
  exact Layout.Valid.set_minimum heap queue layout valid (pendingMinimum heap layout)










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














































theorem table_write_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (degree value : Int) :
    snapshot (heap.write layout.table degree value) layout =
      {snapshot heap layout with table := Algo2Lean.Fibonacci.Rings.write (heap.read layout.table) degree value} := by
  have different := valid.separate
  simp only [Layout.refs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_false_eq_true, and_true, List.nodup_nil, not_or] at different
  have keys : layout.keys ≠ layout.table := different.1.2.2.2.2.2.2.2
  have parents : layout.parents ≠ layout.table := different.2.1.2.2.2.2.2.2
  have children : layout.children ≠ layout.table := different.2.2.1.2.2.2.2.2
  have left : layout.left ≠ layout.table := different.2.2.2.1.2.2.2.2
  have right : layout.right ≠ layout.table := different.2.2.2.2.1.2.2.2
  have degrees : layout.degrees ≠ layout.table := different.2.2.2.2.2.1.2.2
  have marks : layout.marks ≠ layout.table := different.2.2.2.2.2.2.1.2
  have present : layout.present ≠ layout.table := different.2.2.2.2.2.2.2
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, Heap.read, Heap.write,
    Algo2Lean.Fibonacci.Rings.write, keys, parents, children, left, right, degrees, marks, present]













end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis

theorem detach_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) :
    snapshot (detachHeap heap queue layout) (detachLayout heap layout) =
      (snapshot heap layout).detachMinimum := by
  have keys_left : layout.keys ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_right : layout.keys ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_left : layout.parents ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have parents_right : layout.parents ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_left : layout.children ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have children_right : layout.children ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_right : layout.left ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have right_left : layout.right ≠ layout.left := Ne.symm left_right
  have degrees_left : layout.degrees ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_right : layout.degrees ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_left : layout.marks ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have marks_right : layout.marks ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_left : layout.present ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_right : layout.present ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_left : layout.table ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_right : layout.table ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, detachHeap, detachLayout, pendingMinimum, removeHeap,
    set_FibonacciHeap_minimum, Heap.read, Heap.write, Heap.writeField, Heap.tick,
    Algo2Lean.Fibonacci.Snapshot.detachMinimum, Algo2Lean.Fibonacci.Rings.removeLeft,
    Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write,
    keys_left, keys_right, parents_left, parents_right, children_left, children_right, left_right, right_left, degrees_left, degrees_right, marks_left, marks_right, present_left, present_right, table_left, table_right]






theorem detach_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (clock : String) :
    (detachHeap heap queue layout).clocks clock = heap.clocks clock + Clocks.single "heap_root_scans" 1 clock := by
  by_cases clock = "heap_root_scans" <;> simp_all [detachHeap, removeHeap, Heap.tick, Clocks.single, set_FibonacciHeap_minimum, Heap.writeField]






/-- Realize the finite pending-root phase. The continuation can use any verified
    reconstruction of its final buckets; clocks are counted independently. -/
theorem realize_root_consumption (before after : Algo2Lean.Fibonacci.Snapshot)
    (maximum finalMaximum : Int) (roots links : Nat)
    (run : Algo2Lean.Fibonacci.RootConsumption before maximum after finalMaximum roots links)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ tailHeap tailLayout,
      tailLayout.Valid tailHeap queue ∧ snapshot tailHeap tailLayout = after ∧
      (∀ finalHeap finalLayout, RebuildEffect queue finalMaximum tailHeap tailLayout 0 finalHeap finalLayout →
        ConsumeEffect queue heap layout maximum finalHeap finalLayout roots links) ∧
      (∀ clock, tailHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_root_scans" roots clock +
        Clocks.single "heap_comparisons" links clock + Clocks.single "heap_links" links clock) := by
  induction run generalizing heap layout with
  | done state maximum empty =>
    refine ⟨heap, layout, valid, observed, ?_, ?_⟩
    · intro finalHeap finalLayout rebuild
      apply ConsumeEffect.done _ rebuild
      change (snapshot heap layout).minimum < 0
      rw [observed]
      exact empty
    · intro clock
      simp [Clocks.single]
  | @step before merged after maximum vertex degree finalMaximum links roots tailLinks nonempty collisions rest ih =>
    have detachedSnapshot : snapshot (detachHeap heap queue layout) (detachLayout heap layout) = before.detachMinimum := by
      rw [detach_snapshot heap queue layout valid, observed]
    have detachedValid := detach_layout heap queue layout valid
    obtain ⟨mergedHeap, collisionEffect, mergedValid, mergedSnapshot, collisionClocks⟩ :=
      realize_bucket_collisions _ _ _ _ _ _ _ collisions
        (detachHeap heap queue layout) queue (detachLayout heap layout) detachedValid detachedSnapshot
    have minimum : layout.minimum = before.minimum := congrArg Algo2Lean.Fibonacci.Snapshot.minimum observed
    have inputDegree : before.detachMinimum.degrees before.minimum =
        (detachHeap heap queue layout).read layout.degrees layout.minimum := by
      rw [← detachedSnapshot, ← minimum]
      rfl
    have storedSnapshot : snapshot (mergedHeap.write layout.table degree vertex) (detachLayout heap layout) =
        {merged with table := Algo2Lean.Fibonacci.Rings.write merged.table degree vertex} := by
      calc
        _ = {(snapshot mergedHeap (detachLayout heap layout)) with table := Algo2Lean.Fibonacci.Rings.write (snapshot mergedHeap (detachLayout heap layout)).table degree vertex} :=
            table_write_snapshot mergedHeap queue (detachLayout heap layout) mergedValid degree vertex
        _ = _ := by rw [mergedSnapshot]
    obtain ⟨tailHeap, tailLayout, tailValid, tailSnapshot, continuation, tailClocks⟩ :=
      ih (mergedHeap.write layout.table degree vertex) (detachLayout heap layout)
        (Layout.Valid.write _ _ _ mergedValid _ _ _) storedSnapshot
    refine ⟨tailHeap, tailLayout, tailValid, tailSnapshot, ?_, ?_⟩
    · intro finalHeap finalLayout rebuild
      apply ConsumeEffect.next (by omega)
        (by rw [inputDegree, ← minimum] at collisionEffect; exact collisionEffect)
        (continuation finalHeap finalLayout rebuild)
    · intro clock
      rw [tailClocks]
      change mergedHeap.clocks clock + _ + _ + _ = _
      rw [collisionClocks, detach_clocks]
      by_cases clock = "heap_root_scans" <;> by_cases clock = "heap_comparisons" <;>
        by_cases clock = "heap_links" <;> simp_all [Clocks.single] <;> omega






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
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (maximum finalMaximum : Int) (roots links : Nat),
      Algo2Lean.Fibonacci.RootConsumption before maximum after finalMaximum roots links →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Exists.{1} fun tailHeap =>
                Exists.{1} fun tailLayout =>
                  tailLayout.Valid tailHeap queue ∧
                    Eq.{1} (FibonacciModuleAnalysis.snapshot tailHeap tailLayout) after ∧
                      (∀ (finalHeap : Algo2LeanGenerated.Heap)
                          (finalLayout : FibonacciModuleAnalysis.Layout),
                          FibonacciModuleAnalysis.RebuildEffect queue finalMaximum tailHeap tailLayout
                              (0 : Int) finalHeap finalLayout →
                            FibonacciModuleAnalysis.ConsumeEffect queue heap layout maximum finalHeap
                              finalLayout roots links) ∧
                        ∀ (clock : String),
                          Eq.{1} (tailHeap.clocks clock)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (heap.clocks clock)
                                  (Algo2LeanGenerated.Clocks.single "heap_root_scans" roots clock))
                                (Algo2LeanGenerated.Clocks.single "heap_comparisons" links clock))
                              (Algo2LeanGenerated.Clocks.single "heap_links" links clock)) :=
  FibonacciModuleAnalysis.realize_root_consumption
