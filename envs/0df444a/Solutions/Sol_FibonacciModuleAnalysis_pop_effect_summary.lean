-- Prove2me | solution 1 for FibonacciModuleAnalysis.pop_effect_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:10.188979+00:00
-- url     : https://prove2.me/submissions/ec0d43e8-0696-4ee0-aa6b-22cef246b476

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary


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


theorem remove_from_ring_summary (heap : Heap) (queue : Ref_FibonacciHeap)
    (layout : Layout) (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.remove_from_ring.Call heap (queue, vertex)
      (removeHeap heap layout vertex) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc8 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc7 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc6 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc5 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc4 _ _ _
    (by simp [valid.readLeft, valid.leftAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc3 _ _ _
    (by simp [valid.readRight, valid.rightAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_remove_from_ring_pc2 _ _ _)
  simp only [left_write, right_write, valid.readLeft, valid.readRight,
    Option.getD_some, removeHeap]
  exact Reaches.single (Step.FibonacciHeap_remove_from_ring_pc1 _ _ _)

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



/-- An empty queue returns the sentinel and charges one public operation. -/
theorem pop_empty_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (empty : layout.minimum < 0) :
    FibonacciHeap.pop_min.Call heap queue (heap.tick "heap_operations") (-1) := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc42 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc41 _ _ _
    (by simp [valid.readMinimum]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc40 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc39_true _ _ _
    (by simp [valid.readMinimum, empty]))
  apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc38 _ _ _)
  exact Reaches.single (Step.FibonacciHeap_pop_min_pc37 _ _ _)









































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









theorem extraction_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    (extractionLayout layout).Valid (extractionHeap heap queue layout vertex) queue := by
  apply Layout.Valid.set_size
  apply Layout.Valid.write
  exact remove_preserves_layout heap queue layout valid vertex







/-- Every finite local promotion/extraction effect is an actual compiled call.
    The only external premise inside the effect is the separate consolidation call. -/
theorem pop_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (output : Int) (count : Nat)
    (effect : PopEffect queue heap layout after finalLayout output count) :
    FibonacciHeap.pop_min.Call heap queue after output := by
  have finish : ∀ before current final lastLayout vertex,
      ExtractionEffect queue vertex before current final lastLayout → current.Valid before queue →
      ∀ (state : State_FibonacciHeap_pop_min) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_pop_min 19
        {state with v0 := queue, v1 := vertex}) stack)
        (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
    intro before current final lastLayout vertex execution ready state stack
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc19 _ _ _
      (by simp [ready.readRight, ready.rightAllocated]))
    simp only [ready.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc18 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc17 _ _ _ ready.object)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc16 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc15 _ _ _)
    apply Reaches.trans ((remove_from_ring_summary before queue current ready vertex).2 _)
    have removed := remove_preserves_layout before queue current ready vertex
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc14 _ _ _
      (by simp [removed.readPresent, removed.presentAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc13 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc12 _ _ _
      (by simp [removed.readSize]))
    simp only [size_write, removed.readPresent, removed.readSize, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc11 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc10 _ _ _ removed.object)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc9 _ _ _)
    have resized := extraction_layout before queue current ready vertex
    cases execution with
    | last onlyRoot =>
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc8_true _ _ _
        (by simp [onlyRoot]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc3 _ _ _ resized.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_pop_min_pc1 _ _ _)
    | consolidate moreRoots call resultLayout =>
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc8_false _ _ _
        (by simp [moreRoots]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc7 _ _ _ resized.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc6 _ _ _)
      have selected := Layout.Valid.set_minimum _ _ _ resized (before.read current.right vertex)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc5 _ _ _ selected.object)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc4 _ _ _)
      apply Reaches.trans (call.2 _)
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_pop_min_pc1 _ _ _)
  have loop : ∀ vertex before current promoted promotedLayout count,
      PromotionEffect queue vertex before current promoted promotedLayout count →
      current.Valid before queue →
      ∀ final lastLayout, ExtractionEffect queue vertex promoted promotedLayout final lastLayout →
      ∀ (state : State_FibonacciHeap_pop_min) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_pop_min 21
        {state with v0 := queue, v1 := vertex}) stack)
        (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
    intro vertex before current promoted promotedLayout count execution
    induction execution with
    | done before current childless =>
      intro ready final lastLayout extraction state stack
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc21 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc20_false _ _ _
        (by simp [ready.readChildren]; omega))
      simpa only [ready.readChildren, Option.getD_some] using
        finish before current final lastLayout vertex extraction ready
        {state with t14 := decide (before.read current.children vertex ≥ 0)} stack
    | @next before promoted current promotedLayout count hasChild rest ih =>
      intro ready final lastLayout extraction state stack
      have advance : ∀ (locals : State_FibonacciHeap_pop_min),
          Reaches Step (.active (promotionHeaderHeap before current vertex)
            (.fn_FibonacciHeap_pop_min 31 {locals with v0 := queue, v1 := vertex, v2 := before.read current.children vertex}) stack)
            (resumeConfig final (.fn_FibonacciHeap_pop_min vertex) stack) := by
        intro locals
        have headed := promotion_header_layout before queue current ready vertex
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc31 _ _ _
          (by simp [headed.readDegrees, headed.degreesAllocated]))
        simp only [headed.readDegrees, Option.getD_some]
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc30 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc29 _ _ _ headed.object)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc28 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc27 _ _ _)
        have decreased := Layout.Valid.write _ _ _ headed current.degrees vertex
          ((promotionHeaderHeap before current vertex).read current.degrees vertex - 1)
        apply Reaches.trans ((remove_from_ring_summary _ _ _ decreased
          (before.read current.children vertex)).2 _)
        have detached := promotion_detached_layout before queue current ready vertex
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc26 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc25 _ _ _ detached.object)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc24 _ _ _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc23 _ _ _)
        apply Reaches.trans ((add_root_summary _ _ _ detached
          (before.read current.children vertex)).2 _)
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc22 _ _ _)
        exact ih (promotion_layout before queue current ready vertex) final lastLayout extraction
          {locals with v2 := before.read current.children vertex, t15 := (), t16 := queue, t17 := before.read current.children vertex, t18 := (), t19 := queue, t20 := before.read current.children vertex} stack
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc21 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc20_true _ _ _
        (by simp [ready.readChildren, hasChild]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc36 _ _ _
        (by simp [ready.readChildren, ready.childrenAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc35 _ _ _
        (by simp [ready.readRight, ready.rightAllocated]))
      simp only [ready.readChildren, ready.readRight, Option.getD_some]
      by_cases onlyChild : before.read current.right (before.read current.children vertex) =
          before.read current.children vertex
      · apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc34_true _ _ _
          (by simp [onlyChild]))
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc32 _ _ _
          (by simp [ready.readChildren, ready.childrenAllocated]))
        simpa only [promotionHeaderHeap, if_pos onlyChild, ready.readChildren, Option.getD_some] using
          advance {state with t14 := decide (before.read current.children vertex ≥ 0), t21 := decide (before.read current.right (before.read current.children vertex) = before.read current.children vertex)}
      · apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc34_false _ _ _
          (by simp [onlyChild]))
        apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc33 _ _ _
          (by simp [ready.readChildren, ready.childrenAllocated, ready.readRight, ready.rightAllocated]))
        simpa only [promotionHeaderHeap, if_neg onlyChild, ready.readChildren,
          ready.readRight, Option.getD_some] using
          advance {state with t14 := decide (before.read current.children vertex ≥ 0), t21 := decide (before.read current.right (before.read current.children vertex) = before.read current.children vertex)}
  cases effect with
  | empty empty => exact pop_empty_summary heap queue layout valid empty
  | @nonempty promoted after promotedLayout finalLayout count nonempty promote extract =>
    refine ⟨valid.object, ?_⟩
    intro stack
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc42 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc41 _ _ _
      (by simp [valid.readMinimum]))
    simp only [minimum_tick, valid.readMinimum, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc40 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_pop_min_pc39_false _ _ _
      (by simp; omega))
    exact loop layout.minimum (heap.tick "heap_operations") layout promoted promotedLayout count
      promote (Layout.Valid.tick _ _ _ valid _ _) after finalLayout extract
      {t22 := decide (layout.minimum < 0)} stack

















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
    ∀ (heap after : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout finalLayout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (output : Int) (count : Nat),
          FibonacciModuleAnalysis.PopEffect queue heap layout after finalLayout output count →
            Algo.fibonacci_heap.FibonacciHeap.pop_min.Call heap queue after output :=
  FibonacciModuleAnalysis.pop_effect_summary
