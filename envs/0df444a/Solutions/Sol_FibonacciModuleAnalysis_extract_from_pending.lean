-- Prove2me | solution 1 for FibonacciModuleAnalysis.extract_from_pending
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:01:01.725991+00:00
-- url     : https://prove2.me/submissions/ce2ef3a4-b477-4686-9f12-d0984d5fd05f

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_consolidate_from_forest


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

theorem Layout.Valid.set_size (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (size : Int) :
    { layout with size := size }.Valid (set_FibonacciHeap_size heap queue size) queue := by
  constructor
  · simpa [set_FibonacciHeap_size, is_FibonacciHeap] using valid.object
  · simpa [field_FibonacciHeap_keys, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readKeys
  · simpa [field_FibonacciHeap_parents, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readParents
  · simpa [field_FibonacciHeap_children, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readChildren
  · simpa [field_FibonacciHeap_left, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readLeft
  · simpa [field_FibonacciHeap_right, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readRight
  · simpa [field_FibonacciHeap_degrees, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readDegrees
  · simpa [field_FibonacciHeap_marks, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMarks
  · simpa [field_FibonacciHeap_present, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readPresent
  · simpa [field_FibonacciHeap_table, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readTable
  · simpa [field_FibonacciHeap_minimum, set_FibonacciHeap_size, is_FibonacciHeap]
      using valid.readMinimum
  · exact field_FibonacciHeap_size_set heap queue size valid.object
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













































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis























theorem extraction_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (extractionLayout layout).Valid (extractionHeap heap queue layout vertex) queue := by
  apply Layout.Valid.set_size
  apply Layout.Valid.write
  exact remove_preserves_layout heap queue layout valid vertex

























-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.
























































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis











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

















end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis

open Algo2Lean.Fibonacci.Rings



































end FibonacciModuleAnalysis


namespace FibonacciModuleAnalysis



















































































































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

theorem link_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (child parent : Int) :
    heap.Modifies (linkHeap heap layout child parent) layout.refs [queue] := by
  unfold linkHeap linkRingHeap
  dsimp only
  split <;> simp only [linkHeaderHeap]
  all_goals repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.tick
  all_goals first | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]

theorem collision_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex degree : Int) :
    heap.Modifies (collisionHeap heap layout vertex degree) layout.refs [queue] := by
  have ready := ((Heap.Modifies.refl heap layout.refs [queue]).write layout.table degree (-1)
    (by simp [Layout.refs])).tick "heap_comparisons"
  exact ready.trans (link_frame _ queue layout _ _)

theorem detach_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) :
    heap.Modifies (detachHeap heap queue layout) layout.refs [queue] := by
  have prepare := (Heap.Modifies.refl heap layout.refs [queue]).writeField queue "minimum"
    (.intValue (pendingMinimum heap layout)) (by simp)
  exact (prepare.trans (remove_frame _ queue layout _)).tick "heap_root_scans"

theorem rebuild_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (degree : Int) :
    heap.Modifies (rebuildHeap heap queue layout degree) layout.refs [queue] := by
  have clear := ((Heap.Modifies.refl heap layout.refs [queue]).tick "heap_degree_scans").write
    layout.table degree (-1) (by simp [Layout.refs])
  unfold rebuildHeap
  dsimp only
  split
  · exact clear
  · exact clear.trans (add_root_frame _ queue layout _)



theorem RebuildEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum degree : Int}
    (effect : RebuildEffect queue maximum heap layout degree after finalLayout) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done => exact ⟨.refl _ _ _, rfl⟩
  | @step before after current final degree inside rest ih =>
    rw [rebuild_layout_refs] at ih
    exact ⟨(rebuild_frame before queue current degree).trans ih.1, ih.2⟩

theorem CollisionEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout : Layout} {vertex degree finalVertex finalDegree : Int} {links : Nat}
    (effect : CollisionEffect layout heap vertex degree after finalVertex finalDegree links) :
    heap.Modifies after layout.refs [queue] := by
  induction effect with
  | done => exact .refl _ _ _
  | step occupied rest ih => exact (collision_frame _ queue _ _ _).trans ih

theorem ConsumeEffect.frame {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {maximum : Int} {roots links : Nat}
    (effect : ConsumeEffect queue heap layout maximum after finalLayout roots links) :
    heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs := by
  induction effect with
  | done empty rebuild => exact rebuild.frame
  | @next before merged after current final maximum vertex degree links tailRoots tailLinks pending collisions rest ih =>
    have changed := (detach_frame before queue current).trans (collisions.frame (queue := queue))
    have stored := changed.write current.table degree vertex (by simp [Layout.refs])
    exact ⟨stored.trans ih.1, ih.2⟩

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









theorem remove_minimum_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (removeMinimumLayout heap layout vertex).Valid (removeMinimumHeap heap queue layout vertex) queue :=
  Layout.Valid.set_minimum _ _ _ (extraction_layout heap queue layout valid vertex) _







theorem remove_minimum_frame (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout) (vertex : Int) :
    heap.Modifies (removeMinimumHeap heap queue layout vertex) layout.refs [queue] := by
  unfold removeMinimumHeap extractionHeap set_FibonacciHeap_minimum set_FibonacciHeap_size
  repeat' first | apply Heap.Modifies.write | apply Heap.Modifies.writeField
  all_goals first | exact remove_frame _ _ _ _ | exact Heap.Modifies.refl _ _ _ | simp [Layout.refs]


/-- Finish a minimum deletion by reusing the independently verified
    consolidation contract; the empty case performs no additional work. -/
theorem extract_from_pending (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) (pending : Algo2Lean.Fibonacci.Forest)
    (represented : Algo2Lean.Fibonacci.SplitRepresented
      (snapshot (removeMinimumHeap heap queue layout vertex) (removeMinimumLayout heap layout vertex)) pending [])
    (scratch : ∀ degree, (removeMinimumHeap heap queue layout vertex).read layout.table degree < 0) :
    ∃ after finalLayout forest links scans comparisons,
      ExtractionEffect queue vertex heap layout after finalLayout ∧ QueueRep after queue finalLayout forest ∧
      forest.entries.Perm pending.entries ∧ forest.marks = pending.marks ∧
      links + forest.length = pending.length ∧ forest.length ≤ 2 * pending.entries.length.log2 + 2 ∧
      scans ≤ 2 * pending.entries.length.log2 + 2 ∧ comparisons ≤ forest.length ∧
      heap.Modifies after layout.refs [queue] ∧ finalLayout.refs = layout.refs ∧
      ∀ clock, after.clocks clock = heap.clocks clock +
        Clocks.single "heap_root_scans" pending.length clock +
        Clocks.single "heap_comparisons" (links + comparisons) clock +
        Clocks.single "heap_links" links clock + Clocks.single "heap_degree_scans" scans clock := by
  let removed := removeMinimumHeap heap queue layout vertex
  let current := removeMinimumLayout heap layout vertex
  have ready : current.Valid removed queue := remove_minimum_layout heap queue layout valid vertex
  have framed : heap.Modifies removed layout.refs [queue] := remove_minimum_frame heap queue layout vertex
  by_cases last : heap.read layout.right vertex = vertex
  · have minimum : (snapshot removed current).minimum = -1 := by
      simp only [snapshot, current, removeMinimumLayout, last, ↓reduceIte]
    have empty : pending = [] := by
      rcases represented.cursor with empty | ⟨root, member, pointer⟩
      · exact empty.1
      · have nonnegative := represented.nonnegative root.vertex root.key
          (List.mem_flatMap.mpr ⟨root, by simpa using member, root.root_entry⟩)
        change (snapshot removed current).minimum = root.vertex at pointer
        omega
    subst pending
    have rep : Algo2Lean.Fibonacci.Represented (snapshot removed current) [] :=
      ⟨represented.valid, represented.pendingRing, represented.stored,
        represented.nonnegative, represented.presence, represented.size,
        Or.inl ⟨rfl, minimum⟩, scratch⟩
    have effect : ExtractionEffect queue vertex heap layout removed current := by
      simpa only [removed, current, removeMinimumHeap, removeMinimumLayout, last, ↓reduceIte] using
        (ExtractionEffect.last (queue := queue) (layout := layout) last)
    refine ⟨removed, current, [], 0, 0, 0, effect, ⟨ready, rep⟩,
      .refl _, rfl, by simp, by simp, by simp, by simp, framed, rfl, ?_⟩
    intro clock
    change heap.clocks clock = _
    simp [Clocks.single]
  · obtain ⟨after, finalLayout, forest, links, scans, comparisons, call, effect, finalRep,
        entries, marks, rootCount, rootBound, scanBound, comparisonBound, cost⟩ :=
      consolidate_from_forest removed queue current ready pending represented scratch
    have called : FibonacciHeap.consolidate.Call
        (set_FibonacciHeap_minimum (extractionHeap heap queue layout vertex)
          queue (heap.read layout.right vertex)) queue after () := by
      simpa only [removed, removeMinimumHeap, if_neg last] using call
    refine ⟨after, finalLayout, forest, links, scans, comparisons,
      .consolidate last called finalRep.layoutValid, finalRep, entries, marks,
      rootCount, rootBound, scanBound, comparisonBound,
      framed.trans effect.frame.1, effect.frame.2, ?_⟩
    intro clock
    have monotone := consolidation_clocks_monotone removed after queue call clock
    have counted := congrFun cost clock
    change after.clocks clock - heap.clocks clock = _ at counted
    change heap.clocks clock ≤ after.clocks clock at monotone
    omega






end FibonacciModuleAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex : Int) (pending : Algo2Lean.Fibonacci.Forest),
          Algo2Lean.Fibonacci.SplitRepresented
              (FibonacciModuleAnalysis.snapshot
                (FibonacciModuleAnalysis.removeMinimumHeap heap queue layout vertex)
                (FibonacciModuleAnalysis.removeMinimumLayout heap layout vertex))
              pending List.nil.{0} →
            (∀ (degree : Int),
                LT.lt.{0}
                  ((FibonacciModuleAnalysis.removeMinimumHeap heap queue layout vertex).read
                    layout.table degree)
                  (0 : Int)) →
              Exists.{1} fun after =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun forest =>
                    Exists.{1} fun links =>
                      Exists.{1} fun scans =>
                        Exists.{1} fun comparisons =>
                          FibonacciModuleAnalysis.ExtractionEffect queue vertex heap layout after
                              finalLayout ∧
                            FibonacciModuleAnalysis.QueueRep after queue finalLayout forest ∧
                              List.Perm.{0} forest.entries pending.entries ∧
                                Eq.{1} forest.marks pending.marks ∧
                                  Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} forest))
                                      (List.length.{0} pending) ∧
                                    LE.le.{0} (List.length.{0} forest)
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (2 : Nat)
                                            (List.length.{0} pending.entries).log2)
                                          (2 : Nat)) ∧
                                      LE.le.{0} scans
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                                              (List.length.{0} pending.entries).log2)
                                            (2 : Nat)) ∧
                                        LE.le.{0} comparisons (List.length.{0} forest) ∧
                                          heap.Modifies after layout.refs
                                              (List.cons.{0} queue List.nil.{0}) ∧
                                            Eq.{1} finalLayout.refs layout.refs ∧
                                              ∀ (clock : String),
                                                Eq.{1} (after.clocks clock)
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HAdd.hAdd.{0, 0, 0}
                                                        (HAdd.hAdd.{0, 0, 0} (heap.clocks clock)
                                                          (Algo2LeanGenerated.Clocks.single
                                                            "heap_root_scans" (List.length.{0} pending)
                                                            clock))
                                                        (Algo2LeanGenerated.Clocks.single
                                                          "heap_comparisons"
                                                          (HAdd.hAdd.{0, 0, 0} links comparisons)
                                                          clock))
                                                      (Algo2LeanGenerated.Clocks.single "heap_links"
                                                        links clock))
                                                    (Algo2LeanGenerated.Clocks.single
                                                      "heap_degree_scans" scans clock)) :=
  FibonacciModuleAnalysis.extract_from_pending
