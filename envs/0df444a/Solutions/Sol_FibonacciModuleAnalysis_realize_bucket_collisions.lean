-- Prove2me | solution 1 for FibonacciModuleAnalysis.realize_bucket_collisions
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:44.023549+00:00
-- url     : https://prove2.me/submissions/e007280c-4a34-401e-bdb1-785f83b12632

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












-- Initialization follows the source allocation order. The exact-effect
-- statement can be reused without opening this method's transition rules.
















































































-- A link's compiled contract is independent of any whole-heap invariant.
-- Its callers separately establish equal degree, key order, and disjoint trees.


theorem link_preserves_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    layout.Valid (linkHeap heap layout child parent) queue := by
  unfold linkHeap
  apply Layout.Valid.tick
  apply Layout.Valid.write
  apply Layout.Valid.write
  unfold linkRingHeap
  dsimp only
  split
  · repeat apply Layout.Valid.write
    exact valid
  · repeat apply Layout.Valid.write
    exact valid












-- The proof composes the checked ring-removal and root-insertion contracts.
-- Their internal transitions are not revisited when a cut is verified.




























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























theorem collision_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    layout.Valid (collisionHeap heap layout vertex degree) queue := by
  apply link_preserves_layout
  apply Layout.Valid.tick
  exact Layout.Valid.write _ _ _ valid _ _ _






























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







































/-- The compiled link performs precisely the shared forest-storage operation. -/
theorem link_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    snapshot (linkHeap heap layout child parent) layout =
      (snapshot heap layout).link child parent := by
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
  by_cases empty : heap.read layout.children parent < 0
  all_goals
    simp only [Heap.read] at empty
    apply snapshot_ext
    all_goals try funext index
    all_goals simp [snapshot, linkHeap, linkRingHeap, linkHeaderHeap, Heap.read, Heap.write, Heap.tick,
      Algo2Lean.Fibonacci.Snapshot.link, Algo2Lean.Fibonacci.Rings.write,
      Algo2Lean.Fibonacci.Rings.insertBeforeLeft, Algo2Lean.Fibonacci.Rings.insertBeforeRight,
      empty, keys_parents, keys_children, keys_left, keys_right, keys_degrees, keys_marks,
      parents_children, parents_left, parents_right, parents_degrees, parents_marks, children_left,
      children_right, children_degrees, children_marks, left_right, left_degrees, left_marks,
      right_degrees, right_marks, degrees_marks, Ne.symm parents_children, Ne.symm parents_left,
      Ne.symm parents_right, Ne.symm parents_degrees, Ne.symm parents_marks, Ne.symm
      parents_present, Ne.symm parents_table, Ne.symm children_left, Ne.symm children_right, Ne.symm
      children_degrees, Ne.symm children_marks, Ne.symm children_present, Ne.symm children_table,
      Ne.symm left_right, Ne.symm left_degrees, Ne.symm left_marks, Ne.symm left_present, Ne.symm
      left_table, Ne.symm right_degrees, Ne.symm right_marks, Ne.symm right_present, Ne.symm
      right_table, Ne.symm degrees_marks, Ne.symm degrees_present, Ne.symm degrees_table, Ne.symm
      marks_present, Ne.symm marks_table]






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




theorem collision_parent_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    collisionParent heap layout vertex degree = (snapshot heap layout).collisionParent vertex degree := by
  have different : layout.keys ≠ layout.table := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  simp [collisionParent, collisionStart, Algo2Lean.Fibonacci.Snapshot.collisionParent,
    snapshot, Heap.read, Heap.write, different]

theorem collision_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex degree : Int) :
    snapshot (collisionHeap heap layout vertex degree) layout =
      (snapshot heap layout).collision vertex degree := by
  have different : layout.keys ≠ layout.table := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have ready : layout.Valid (collisionStart heap layout degree) queue := Layout.Valid.tick _ _ _ (Layout.Valid.write _ _ _ valid layout.table degree (-1)) "heap_comparisons" 1
  unfold collisionHeap
  rw [link_snapshot (collisionStart heap layout degree) queue layout ready]
  simp only [collisionStart, snapshot_tick, table_write_snapshot heap queue layout valid degree (-1)]
  simp only [collisionChild, collisionParent, collisionStart, Heap.read_tick]
  simp only [Heap.read_write_other_ref _ _ _ _ _ _ different]
  unfold Algo2Lean.Fibonacci.Snapshot.collision
  dsimp only [snapshot]
  split <;> rfl



theorem collision_clocks (heap : Heap) (layout : Layout) (vertex degree : Int) (clock : String) :
    (collisionHeap heap layout vertex degree).clocks clock = heap.clocks clock +
      Clocks.single "heap_comparisons" 1 clock + Clocks.single "heap_links" 1 clock := by
  unfold collisionHeap linkHeap linkRingHeap
  dsimp only
  split <;> by_cases clock = "heap_links" <;> by_cases clock = "heap_comparisons" <;> simp_all [linkHeaderHeap, collisionStart, Heap.tick, Clocks.single]

/-- Every finite mathematical collision trace is realized by the compiled
    pointer operations with precisely one comparison and one link per collision. -/
theorem realize_bucket_collisions (before after : Algo2Lean.Fibonacci.Snapshot)
    (vertex degree finalVertex finalDegree : Int) (links : Nat)
    (run : Algo2Lean.Fibonacci.BucketCollisions before vertex degree after finalVertex finalDegree links)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ finalHeap,
      CollisionEffect layout heap vertex degree finalHeap finalVertex finalDegree links ∧
      layout.Valid finalHeap queue ∧ snapshot finalHeap layout = after ∧
      ∀ clock, finalHeap.clocks clock = heap.clocks clock +
        Clocks.single "heap_comparisons" links clock + Clocks.single "heap_links" links clock := by
  induction run generalizing heap layout with
  | done state vertex degree empty =>
    refine ⟨heap, .done _ _ _ ?_, valid, observed, ?_⟩
    · change (snapshot heap layout).table degree < 0
      rw [observed]
      exact empty
    · intro clock
      simp [Clocks.single]
  | @step state after vertex degree result finalDegree links occupied rest ih =>
    have next : snapshot (collisionHeap heap layout vertex degree) layout = state.collision vertex degree := by
      rw [collision_snapshot heap queue layout valid, observed]
    have parent : collisionParent heap layout vertex degree = state.collisionParent vertex degree := by
      rw [collision_parent_snapshot heap queue layout valid, observed]
    obtain ⟨finalHeap, effect, finalValid, finalObserved, clocks⟩ := ih
      (collisionHeap heap layout vertex degree) layout (collision_layout heap queue layout valid vertex degree) next
    refine ⟨finalHeap, .step ?_ (by simpa only [parent] using effect), finalValid, finalObserved, ?_⟩
    · change 0 ≤ (snapshot heap layout).table degree
      rw [observed]
      exact occupied
    · intro clock
      rw [clocks, collision_clocks]
      by_cases clock = "heap_comparisons" <;> by_cases clock = "heap_links" <;>
        simp_all [Clocks.single, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]









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
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (vertex degree finalVertex finalDegree : Int)
      (links : Nat),
      Algo2Lean.Fibonacci.BucketCollisions before vertex degree after finalVertex finalDegree links →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Exists.{1} fun finalHeap =>
                FibonacciModuleAnalysis.CollisionEffect layout heap vertex degree finalHeap finalVertex
                    finalDegree links ∧
                  layout.Valid finalHeap queue ∧
                    Eq.{1} (FibonacciModuleAnalysis.snapshot finalHeap layout) after ∧
                      ∀ (clock : String),
                        Eq.{1} (finalHeap.clocks clock)
                          (HAdd.hAdd.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0} (heap.clocks clock)
                              (Algo2LeanGenerated.Clocks.single "heap_comparisons" links clock))
                            (Algo2LeanGenerated.Clocks.single "heap_links" links clock)) :=
  FibonacciModuleAnalysis.realize_bucket_collisions
