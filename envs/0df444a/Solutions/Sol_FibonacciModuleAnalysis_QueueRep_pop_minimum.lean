-- Prove2me | solution 1 for FibonacciModuleAnalysis.QueueRep.pop_minimum
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:02:44.028446+00:00
-- url     : https://prove2.me/submissions/b70074a6-6706-4078-944f-64a506d7c8b6

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_pop_effect_summary
import Theorems.Thm_FibonacciModuleAnalysis_extract_from_pending
import Theorems.Thm_Algo2Lean_Fibonacci_Represented_delete_minimum


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci
































/-- Enlarging the finite size bound can only enlarge its logarithmic budget. -/
theorem log2_mono {smaller larger : Nat} (bound : smaller ≤ larger) :
    smaller.log2 ≤ larger.log2 := by
  by_cases zero : smaller = 0
  · simp [zero]
  · have positive : larger ≠ 0 := by omega
    exact (Nat.le_log2 positive).mpr (Nat.le_trans (Nat.log2_self_le zero) bound)































































end Algo2Lean.Fibonacci

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite logical forests for the mutable Fibonacci heap.

Vertex handles and keys are mathematical integers. Child lists are newest-first
in link order, matching insertion before the physical child-ring head. A ring
representation still needs to prove that its traversal realizes this finite
forest, with unique handles and the observable parent/mark/degree fields.
-/

namespace Algo2Lean.Fibonacci



























































/-- Local parent-child order implies that the root is a lower bound for every
    key in its subtree, not merely its immediate children. -/
theorem Node.Ordered.root_minimum {node : Node} (ordered : node.Ordered) :
    ∀ vertex key, (vertex, key) ∈ node.entries → node.key ≤ key := by
  induction ordered with
  | make rootBound valid ih =>
    intro vertex key member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, inside⟩
    · exact Int.le_refl _
    · exact Int.le_trans (rootBound child inChildren) (ih child inChildren vertex key inside)

/-- A minimum among the roots is a minimum among all stored vertex/key pairs. -/
theorem Forest.minimum_of_roots {forest : Forest} {minimum : Node}
    (ordered : forest.Ordered) (present : minimum ∈ forest)
    (leastRoot : ∀ root ∈ forest, minimum.key ≤ root.key) :
    (minimum.vertex, minimum.key) ∈ forest.entries ∧
      ∀ vertex key, (vertex, key) ∈ forest.entries → minimum.key ≤ key := by
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨minimum, present, ?_⟩
    cases minimum
    simp [Node.entries, Node.vertex, Node.key]
  · intro vertex key member
    obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
    exact Int.le_trans (leastRoot root inForest) ((ordered root inForest).root_minimum vertex key inside)























































































end Algo2Lean.Fibonacci

end

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











/-- Storage reads agree with every logical entry, not only the root. -/
theorem Stored.entries {state : Snapshot} {parent : Int} {node : Node}
    (stored : Stored state parent node) :
    ∀ vertex key, (vertex, key) ∈ node.entries →
      state.keys vertex = key ∧ state.present vertex = 1 := by
  induction stored with
  | node key parent mark degree present childHead ring children ih =>
    intro vertex value member
    simp only [Node.entries, List.mem_cons, Prod.mk.injEq, List.mem_flatMap] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨child, inChildren, member⟩
    · exact ⟨key, present⟩
    · exact ih child inChildren vertex value member



theorem Represented.entry {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) {vertex key : Int}
    (member : (vertex, key) ∈ forest.entries) :
    state.keys vertex = key ∧ state.present vertex = 1 := by
  obtain ⟨root, inForest, inside⟩ := List.mem_flatMap.mp member
  exact (represented.stored root inForest).entries vertex key inside



/-- The public minimum pointer identifies a present globally minimum key. -/
theorem Represented.minimum_key {state : Snapshot} {forest : Forest}
    (represented : Represented state forest) (nonempty : forest ≠ []) :
    0 ≤ state.minimum ∧ state.present state.minimum = 1 ∧
      ∀ vertex, state.present vertex ≠ 0 → state.keys state.minimum ≤ state.keys vertex := by
  rcases represented.minimum with ⟨empty, _⟩ | ⟨root, inForest, pointer, least⟩
  · exact False.elim (nonempty empty)
  obtain ⟨rootEntry, minimum⟩ := Forest.minimum_of_roots represented.valid.2.1 inForest least
  have rootValues := represented.entry rootEntry
  rw [pointer]
  refine ⟨represented.nonnegative _ _ rootEntry, rootValues.2, ?_⟩
  intro vertex present
  obtain ⟨key, member⟩ := (represented.presence vertex).mp present
  rw [rootValues.1, (represented.entry member).1]
  exact minimum vertex key member







































































































































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









theorem promotion_header_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (promotionHeaderHeap heap layout vertex) queue := by
  unfold promotionHeaderHeap
  dsimp only
  split <;> exact Layout.Valid.write _ _ _ valid _ _ _

theorem promotion_detached_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    layout.Valid (promotionDetachedHeap heap layout vertex) queue := by
  apply remove_preserves_layout
  apply Layout.Valid.write
  exact promotion_header_layout heap queue layout valid vertex

theorem promotion_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (promotionLayout heap layout vertex).Valid (promotionHeap heap queue layout vertex) queue := by
  apply Layout.Valid.tick
  apply add_root_layout
  exact promotion_detached_layout heap queue layout valid vertex



































-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
























































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis



theorem promotion_layout_nonempty (heap : Heap) (layout : Layout) (vertex : Int)
    (nonempty : 0 ≤ layout.minimum) (hasChild : 0 ≤ heap.read layout.children vertex) :
    0 ≤ (promotionLayout heap layout vertex).minimum := by
  unfold promotionLayout addRootLayout
  rw [if_neg (by omega)]
  dsimp only
  split
  · exact hasChild
  · exact nonempty

/-- A promotion in a nonempty queue charges one promotion and one key comparison. -/
theorem promotion_clocks (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (vertex : Int) (nonempty : 0 ≤ layout.minimum) (clock : String) :
    (promotionHeap heap queue layout vertex).clocks clock = heap.clocks clock +
      Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock := by
  have headerClocks : (promotionHeaderHeap heap layout vertex).clocks = heap.clocks := by
    unfold promotionHeaderHeap
    dsimp only
    split <;> rfl
  unfold promotionHeap addRootHeap
  rw [if_neg (by omega)]
  dsimp only
  split <;> by_cases promotion : clock = "heap_promotions" <;>
    by_cases comparison : clock = "heap_comparisons" <;>
    simp [promotionDetachedHeap, rootHeaderHeap, insertRingHeap, headerClocks,
      removeHeap, set_FibonacciHeap_minimum, Clocks.single, Heap.tick, promotion, comparison, Nat.add_comm]

theorem promotion_effect_clocks (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int) (count : Nat)
    (effect : PromotionEffect queue vertex heap layout after finalLayout count)
    (nonempty : 0 ≤ layout.minimum) (clock : String) :
    after.clocks clock = heap.clocks clock + count *
      (Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock) := by
  induction effect with
  | done _ _ _ => simp
  | @next before after current finalLayout count hasChild rest ih =>
    rw [ih (promotion_layout_nonempty before current vertex nonempty hasChild),
      promotion_clocks before queue current vertex nonempty clock]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]



/-- Valid compiled calls never decrease a clock, including consolidation's nested calls. -/
theorem consolidation_clocks_monotone (heap after : Heap) (queue : Ref_FibonacciHeap)
    (call : FibonacciHeap.consolidate.Call heap queue after ()) (clock : String) :
    heap.clocks clock ≤ after.clocks clock := by
  have resumeHeap (heap : Heap) (result : Result) (stack : Stack) :
      (resumeConfig heap result stack).heap = heap := by cases stack <;> rfl
  have transitions : ∀ before after, Step before after →
      before.heap.clocks clock ≤ after.heap.clocks clock := by
    intro before after transition
    cases transition <;> (try simp only [resumeHeap]) <;> simp [Config.heap,
      set_FibonacciHeap_keys, set_FibonacciHeap_parents, set_FibonacciHeap_children,
      set_FibonacciHeap_left, set_FibonacciHeap_right, set_FibonacciHeap_degrees,
      set_FibonacciHeap_marks, set_FibonacciHeap_present, set_FibonacciHeap_table,
      set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.tick] <;> split <;> omega
  exact (call.2 []).invariant (fun state => heap.clocks clock ≤ state.heap.clocks clock)
    (Nat.le_refl _) (fun before after step earlier => Nat.le_trans earlier (transitions before after step))

theorem extraction_effect_clocks_monotone (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (vertex : Int)
    (effect : ExtractionEffect queue vertex heap layout after finalLayout) (clock : String) :
    heap.clocks clock ≤ after.clocks clock := by
  cases effect with
  | last onlyRoot => exact Nat.le_refl _
  | consolidate moreRoots call resultLayout =>
    exact consolidation_clocks_monotone _ _ _ call clock



/-- Public removal costs split into one operation, the counted child promotions,
    and the separate consolidation cost. The extraction phase contributes no ticks. -/
theorem pop_nonempty_cost (heap promoted after : Heap) (queue : Ref_FibonacciHeap)
    (layout promotedLayout finalLayout : Layout) (count : Nat)
    (nonempty : 0 ≤ layout.minimum)
    (promote : PromotionEffect queue layout.minimum (heap.tick "heap_operations")
      layout promoted promotedLayout count)
    (extract : ExtractionEffect queue layout.minimum promoted promotedLayout after finalLayout) :
    Heap.cost heap after = fun clock => Clocks.single "heap_operations" 1 clock +
      count * (Clocks.single "heap_promotions" 1 clock + Clocks.single "heap_comparisons" 1 clock) +
      Heap.cost promoted after clock := by
  funext clock
  have promotion := promotion_effect_clocks _ _ _ _ _ _ _ promote nonempty clock
  have monotone := extraction_effect_clocks_monotone _ _ _ _ _ _ extract clock
  by_cases operation : clock = "heap_operations" <;>
    simp_all [Heap.cost, Clocks.single] <;> omega











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

/-- Child promotion uses the same pointer changes as a cut; only its clock differs. -/
theorem promotion_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
      (snapshot heap layout).promoteChild vertex := by
  have header : promotionHeaderHeap heap layout vertex =
      cutHeaderHeap heap layout (heap.read layout.children vertex) vertex := by
    simp only [promotionHeaderHeap, cutHeaderHeap]
    split <;> rfl
  have same : snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
      snapshot (cutHeap heap queue layout (heap.read layout.children vertex) vertex)
        (cutLayout heap layout (heap.read layout.children vertex) vertex) := by
    simp only [promotionHeap, promotionLayout, promotionDetachedHeap, cutHeap, cutTailHeap, cutLayout,
      snapshot_tick, header]
  rw [same, cut_snapshot heap queue layout valid]
  rfl

theorem realize_promotions (before after : Algo2Lean.Fibonacci.Snapshot) (vertex : Int) (count : Nat)
    (run : Algo2Lean.Fibonacci.PromotionRun vertex before after count)
    (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (observed : snapshot heap layout = before) :
    ∃ promoted finalLayout, PromotionEffect queue vertex heap layout promoted finalLayout count ∧
      finalLayout.Valid promoted queue ∧ snapshot promoted finalLayout = after := by
  induction run generalizing heap layout with
  | done state childless =>
    refine ⟨heap, layout, .done _ _ ?_, valid, observed⟩
    change (snapshot heap layout).children vertex < 0
    rw [observed]
    exact childless
  | @next before after count hasChild rest ih =>
    have next : snapshot (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex) =
        before.promoteChild vertex := by rw [promotion_snapshot heap queue layout valid, observed]
    obtain ⟨promoted, finalLayout, effect, ready, result⟩ := ih
      (promotionHeap heap queue layout vertex) (promotionLayout heap layout vertex)
      (promotion_layout heap queue layout valid vertex) next
    refine ⟨promoted, finalLayout, .next ?_ effect, ready, result⟩
    change 0 ≤ (snapshot heap layout).children vertex
    rw [observed]
    exact hasChild







theorem remove_minimum_snapshot (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    snapshot (removeMinimumHeap heap queue layout vertex) (removeMinimumLayout heap layout vertex) =
      (snapshot heap layout).extractRoot vertex := by
  have keys_left : layout.keys ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_right : layout.keys ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have keys_present : layout.keys ≠ layout.present := by
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
  have parents_present : layout.parents ≠ layout.present := by
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
  have children_present : layout.children ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_right : layout.left ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have left_present : layout.left ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have right_left : layout.right ≠ layout.left := Ne.symm left_right
  have right_present : layout.right ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_left : layout.degrees ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_right : layout.degrees ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have degrees_present : layout.degrees ≠ layout.present := by
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
  have marks_present : layout.marks ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have present_left : layout.present ≠ layout.left := Ne.symm left_present
  have present_right : layout.present ≠ layout.right := Ne.symm right_present
  have table_left : layout.table ≠ layout.left := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_right : layout.table ≠ layout.right := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  have table_present : layout.table ≠ layout.present := by
    intro same
    have all := valid.separate
    simp_all [Layout.refs, List.nodup_cons]
  apply snapshot_ext
  all_goals try funext index
  all_goals simp [snapshot, removeMinimumHeap, removeMinimumLayout, extractionHeap, extractionLayout,
    removeHeap, set_FibonacciHeap_minimum, set_FibonacciHeap_size, Heap.read, Heap.write, Heap.writeField,
    Algo2Lean.Fibonacci.Snapshot.extractRoot, Algo2Lean.Fibonacci.Rings.removeLeft,
    Algo2Lean.Fibonacci.Rings.removeRight, Algo2Lean.Fibonacci.Rings.write,
    keys_left, keys_right, keys_present, parents_left, parents_right, parents_present, children_left, children_right, children_present, left_right, left_present, right_left, right_present, degrees_left, degrees_right, degrees_present, marks_left, marks_right, marks_present, present_left, present_right, table_left, table_right, table_present]

/-- Promotion frames compose independently of the forest argument. -/
theorem promotion_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (promotionHeap heap queue layout vertex) layout.refs [queue] := by
  have header : heap.Modifies (promotionHeaderHeap heap layout vertex) layout.refs [queue] := by
    unfold promotionHeaderHeap
    dsimp only
    split <;> exact (Heap.Modifies.refl _ _ _).write _ _ _ (by simp [Layout.refs])
  have decreased := header.write layout.degrees vertex ((promotionHeaderHeap heap layout vertex).read layout.degrees vertex - 1) (by simp [Layout.refs])
  have detached := decreased.trans (remove_frame _ queue layout (heap.read layout.children vertex))
  exact (detached.trans (add_root_frame _ queue layout _)).tick "heap_promotions"

theorem PromotionEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {count : Nat}
    (effect : PromotionEffect queue vertex heap layout after finalLayout count) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done => exact ⟨.refl _ _ _, rfl⟩
  | @next before after current final count hasChild rest ih =>
    rw [promotion_layout_refs] at ih
    exact ⟨(promotion_frame before queue current vertex).trans ih.1, ih.2⟩









/-- A represented nonempty queue has a terminating, correct, logarithmically
    amortized minimum extraction, without a supplied execution transcript. -/
theorem QueueRep.pop_minimum {heap : Heap} {queue : Ref_FibonacciHeap} {layout : Layout}
    {forest : Algo2Lean.Fibonacci.Forest} (rep : QueueRep heap queue layout forest)
    (nonempty : forest ≠ []) :
    ∃ after finalLayout afterForest, PopContract heap queue layout forest after finalLayout afterForest := by
  have nonnegative : 0 ≤ layout.minimum := (rep.represented.minimum_key nonempty).1
  obtain ⟨deleted, pending, count, deletion, splitRep, scratch, deletedEntries, rootCount, marksBound, degreeBound⟩ :=
    rep.represented.delete_minimum nonempty
  cases deletion with
  | @finish promoted count promotions =>
    obtain ⟨promotedHeap, promotedLayout, promotionEffect, promotedValid, promotedSnapshot⟩ :=
      realize_promotions _ _ _ _ promotions (heap.tick "heap_operations") queue layout
        (Layout.Valid.tick _ _ _ rep.layoutValid _ _) rfl
    have removedSnapshot : snapshot (removeMinimumHeap promotedHeap queue promotedLayout layout.minimum)
        (removeMinimumLayout promotedHeap promotedLayout layout.minimum) = promoted.extractRoot layout.minimum := by
      rw [remove_minimum_snapshot promotedHeap queue promotedLayout promotedValid, promotedSnapshot]
    obtain ⟨after, finalLayout, afterForest, links, scans, comparisons, extractionEffect, finalRep,
        entries, marks, linkCount, rootsBound, scanBound, comparisonBound, extractionFrame, extractionRefs, extractionClocks⟩ :=
      extract_from_pending promotedHeap queue promotedLayout promotedValid layout.minimum pending
        (by rw [removedSnapshot]; exact splitRep)
        (by
          intro degree
          change (snapshot (removeMinimumHeap promotedHeap queue promotedLayout layout.minimum)
            (removeMinimumLayout promotedHeap promotedLayout layout.minimum)).table degree < 0
          rw [removedSnapshot]
          exact scratch degree)
    have effect : PopEffect queue heap layout after finalLayout layout.minimum count :=
      .nonempty nonnegative promotionEffect extractionEffect
    have promotionFrame := promotionEffect.frame
    have fullFrame : heap.Modifies after layout.refs [queue] :=
      (((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_operations").trans promotionFrame.1).trans
        (by simpa only [promotionFrame.2] using extractionFrame)
    have fullContents : ((layout.minimum, heap.read layout.keys layout.minimum) :: afterForest.entries).Perm forest.entries :=
      (entries.cons _).trans deletedEntries
    have clocks := promotion_effect_clocks _ _ _ _ _ _ _ promotionEffect nonnegative
    have extractionCost : Heap.cost promotedHeap after = fun clock =>
        Clocks.single "heap_root_scans" pending.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
      funext clock
      unfold Heap.cost
      rw [extractionClocks]
      omega
    have popCost := pop_nonempty_cost heap promotedHeap after queue layout promotedLayout finalLayout count
      nonnegative promotionEffect extractionEffect
    have work : heapEventWork heap after = 1 + 2 * count + pending.length + 2 * links + comparisons + scans := by
      simp [heapEventWork, popCost, extractionCost, Clocks.single]
      omega
    refine ⟨after, finalLayout, afterForest, ⟨pop_effect_summary _ _ _ _ _ rep.layoutValid _ _ effect,
      finalRep, fullContents, fullFrame, extractionRefs.trans promotionFrame.2, ?_, ?_⟩⟩
    · intro clock outside
      have notOperation : clock ≠ "heap_operations" := by intro same; exact outside (by simp [heapClocks, same])
      have notPromotions : clock ≠ "heap_promotions" := by intro same; exact outside (by simp [heapClocks, same])
      have notComparisons : clock ≠ "heap_comparisons" := by intro same; exact outside (by simp [heapClocks, same])
      have notRoots : clock ≠ "heap_root_scans" := by intro same; exact outside (by simp [heapClocks, same])
      have notLinks : clock ≠ "heap_links" := by intro same; exact outside (by simp [heapClocks, same])
      have notDegrees : clock ≠ "heap_degree_scans" := by intro same; exact outside (by simp [heapClocks, same])
      rw [extractionClocks, clocks]
      simp [Clocks.single, Heap.tick, notOperation, notPromotions, notComparisons, notRoots, notLinks, notDegrees]
    · have size := deletedEntries.length_eq
      simp only [List.length_cons] at size
      have logBound := Algo2Lean.Fibonacci.log2_mono (show pending.entries.length ≤ forest.entries.length by omega)
      simp only [Algo2Lean.Fibonacci.scaledPotential, Algo2Lean.Fibonacci.potential, Algo2Lean.Fibonacci.Forest.counts]
      rw [work]
      omega

end FibonacciModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        Ne.{1} forest List.nil.{0} →
          Exists.{1} fun after =>
            Exists.{1} fun finalLayout =>
              Exists.{1} fun afterForest =>
                FibonacciModuleAnalysis.PopContract heap queue layout forest after finalLayout
                  afterForest :=
  FibonacciModuleAnalysis.QueueRep.pop_minimum
