-- Prove2me | solution 1 for FibonacciModuleAnalysis.decrease_effect_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:55:10.281814+00:00
-- url     : https://prove2.me/submissions/6b48f70b-9422-4f10-abfd-ce1bfc098256

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_cut_summary


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




theorem cascade_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (vertex : Int) (cuts : Nat)
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts) :
    FibonacciHeap.cascading_cut.Call heap (queue, vertex) after () := by
  have loop : ∀ before current node final finalLayout count,
      CascadeEffect queue before current node final finalLayout count → current.Valid before queue →
      ∀ (state : State_FibonacciHeap_cascading_cut) stack,
      Reaches Step (.active before (.fn_FibonacciHeap_cascading_cut 4
        { state with v0 := queue, v1 := node, v2 := before.read current.parents node }) stack)
        (resumeConfig final (.fn_FibonacciHeap_cascading_cut ()) stack) := by
    intro before current node final finalLayout count execution
    induction execution with
    | root before current node root =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_false _ _ _
        (by simp; omega))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc2 _ _ _)
      exact Reaches.single (Step.FibonacciHeap_cascading_cut_pc1 _ _ _)
    | mark before current node nonroot unmarked =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc16 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc15_true _ _ _
        (by simp [ready.readMarks, unmarked]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc14 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc13 _ _ _)
      simp only [ready.readMarks, Option.getD_some]
      exact Reaches.single (Step.FibonacciHeap_cascading_cut_pc12 _ _ _)
    | @cut before final current finalLayout node count nonroot marked rest ih =>
      intro ready state stack
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc4 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc3_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc16 _ _ _
        (by simp [ready.readMarks, ready.marksAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc15_false _ _ _
        (by simp [ready.readMarks, marked]))
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc11 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc10 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc9 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc8 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc7 _ _ _)
      apply Reaches.trans ((cut_summary before queue current ready node
        (before.read current.parents node)).2 _)
      have nextReady := cut_layout before queue current ready node (before.read current.parents node)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc6 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc5 _ _ _
        (by simpa [nextReady.readParents] using nextReady.parentsAllocated))
      simpa only [ready.readMarks, nextReady.readParents, Option.getD_some] using
        ih nextReady { state with t4 := decide (before.read current.parents node ≥ 0), t5 := (), t6 := queue, t7 := node, t8 := before.read current.parents node, t9 := decide (before.read current.marks node = 0) } stack
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_cascading_cut_pc17 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  simpa only [valid.readParents, Option.getD_some] using
    loop heap layout vertex after finalLayout cuts effect valid {} stack

-- This is a terminating compiled execution, derived from decreasing parents;
-- it does not ask the caller to supply a transcript or a cascade result.















end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis





end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis















































end FibonacciModuleAnalysis

namespace FibonacciModuleAnalysis









































theorem lower_key_layout (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex key : Int) :
    layout.Valid (lowerKeyHeap heap layout vertex key) queue := by
  apply Layout.Valid.write
  apply Layout.Valid.tick
  apply Layout.Valid.tick
  exact valid





theorem CascadeEffect.valid {heap after : Heap} {queue : Ref_FibonacciHeap}
    {layout finalLayout : Layout} {vertex : Int} {cuts : Nat}
    (effect : CascadeEffect queue heap layout vertex after finalLayout cuts)
    (valid : layout.Valid heap queue) : finalLayout.Valid after queue := by
  induction effect with
  | root => exact valid
  | mark => exact Layout.Valid.write _ _ _ valid _ _ _
  | cut nonroot marked rest ih =>
    exact ih (cut_layout _ _ _ valid _ _)

-- The three decrease cases record exact heap effects and reuse a cascade's
-- contract. The initial key update is kept separate from its tree repairs.




theorem decrease_effect_summary (heap after : Heap) (queue : Ref_FibonacciHeap)
    (layout finalLayout : Layout) (valid : layout.Valid heap queue) (vertex key : Int)
    (present : heap.read layout.present vertex ≠ 0) (smaller : key < heap.read layout.keys vertex)
    (cuts : Nat)
    (effect : DecreaseEffect queue vertex key (lowerKeyHeap heap layout vertex key)
      layout after finalLayout cuts) :
    FibonacciHeap.push_or_decrease.Call heap (queue, vertex, key) after () := by
  have finish (prepared : Heap) (current : Layout) (ready : current.Valid prepared queue)
      (state : State_FibonacciHeap_push_or_decrease) (stack : Stack) :
      Reaches Step (.active prepared (.fn_FibonacciHeap_push_or_decrease 6
        { state with v0 := queue, v1 := vertex }) stack)
        (resumeConfig (finishDecreaseHeap prepared queue current vertex)
          (.fn_FibonacciHeap_push_or_decrease ()) stack) := by
    apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc6 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc5 _ _ _
      (by simp [ready.readKeys, ready.readMinimum, ready.keysAllocated]))
    by_cases lower : prepared.read current.keys vertex < prepared.read current.keys current.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc4_true _ _ _
        (by simp [ready.readKeys, ready.readMinimum, lower]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc3 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc2 _ _ _)
      simp only [finishDecreaseHeap, if_pos lower]
      exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc1 _ _ _)
    · apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc4_false _ _ _
        (by simp [ready.readKeys, ready.readMinimum, lower]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc2 _ _ _)
      simp only [finishDecreaseHeap, if_neg lower]
      exact Reaches.single (Step.FibonacciHeap_push_or_decrease_pc1 _ _ _)
  have tail : ∀ prepared current final finalLayout count,
      DecreaseEffect queue vertex key prepared current final finalLayout count →
      current.Valid prepared queue → ∀ (state : State_FibonacciHeap_push_or_decrease) stack,
      Reaches Step (.active prepared (.fn_FibonacciHeap_push_or_decrease 20
        { state with v0 := queue, v1 := vertex, v2 := key, v3 := prepared.read current.parents vertex }) stack)
        (resumeConfig final (.fn_FibonacciHeap_push_or_decrease ()) stack) := by
    intro prepared current final finalLayout count execution ready state stack
    cases execution with
    | root prepared root =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_false _ _ _ (by simp; omega))
      exact finish prepared current ready
        { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0) } stack
    | ordered prepared nonroot ordered =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc18 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc17 _ _ _
        (by simp [ready.readKeys, ready.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc16_false _ _ _
        (by simp [ready.readKeys]; omega))
      simpa only [keys_tick, ready.readKeys, Option.getD_some, Heap.read_tick] using
        finish (prepared.tick "heap_comparisons") current (Layout.Valid.tick _ _ _ ready _ _)
          { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0), t7 := decide (key < prepared.read current.keys (prepared.read current.parents vertex)) } stack
    | @cut middle _ middleLayout count nonroot unordered cascade =>
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc20 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc19_true _ _ _ (by simp [nonroot]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc18 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc17 _ _ _
        (by simp [ready.readKeys, ready.keysAllocated]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc16_true _ _ _
        (by simp [ready.readKeys, unordered]))
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc15 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc14 _ _ _ ready.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc13 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc12 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc11 _ _ _)
      have comparedReady := Layout.Valid.tick _ _ _ ready "heap_comparisons" 1
      apply Reaches.trans ((cut_summary _ queue current comparedReady vertex
        (prepared.read current.parents vertex)).2 _)
      have cutReady := cut_layout _ queue current comparedReady vertex
        (prepared.read current.parents vertex)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc10 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc9 _ _ _ cutReady.object)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc8 _ _ _)
      apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc7 _ _ _)
      apply Reaches.trans ((cascade_effect_summary _ middle queue _ middleLayout cutReady
        (prepared.read current.parents vertex) count cascade).2 _)
      simpa only [keys_tick, ready.readKeys, Option.getD_some, Heap.read_tick] using!
        finish middle middleLayout (cascade.valid cutReady)
          { state with v2 := key, v3 := prepared.read current.parents vertex, t6 := decide (prepared.read current.parents vertex ≥ 0), t7 := decide (key < prepared.read current.keys (prepared.read current.parents vertex)), t8 := (), t9 := queue, t10 := prepared.read current.parents vertex, t11 := (), t12 := queue, t13 := vertex, t14 := prepared.read current.parents vertex } stack
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc44 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc43 _ _ _
    (by simp [valid.readPresent, valid.presentAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc42_false _ _ _
    (by simp [valid.readPresent, present]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc27 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc26 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc25_false _ _ _
    (by simp [valid.readKeys]; omega))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc22 _ _ _
    (by simp [valid.readKeys, valid.keysAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_push_or_decrease_pc21 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  simpa only [lowerKeyHeap, keys_tick, parents_write, parents_tick, valid.readKeys,
    valid.readParents, valid.readPresent, present_tick, Option.getD_some, Heap.read_tick] using
    tail (lowerKeyHeap heap layout vertex key) layout after finalLayout cuts effect
      (lower_key_layout _ _ _ valid _ _)
      { t15 := decide (key ≥ heap.read layout.keys vertex),
        t17 := decide (heap.read layout.present vertex = 0) } stack



















































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
        ∀ (vertex key : Int),
          Ne.{1} (heap.read layout.present vertex) (0 : Int) →
            LT.lt.{0} key (heap.read layout.keys vertex) →
              ∀ (cuts : Nat),
                FibonacciModuleAnalysis.DecreaseEffect queue vertex key
                    (FibonacciModuleAnalysis.lowerKeyHeap heap layout vertex key) layout after
                    finalLayout cuts →
                  Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                    (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () :=
  FibonacciModuleAnalysis.decrease_effect_summary
