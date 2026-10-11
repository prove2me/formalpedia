-- Prove2me | solution 1 for FibonacciModuleAnalysis.cut_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:53:52.254019+00:00
-- url     : https://prove2.me/submissions/c816a3fb-7afb-4139-9e8c-6c85a2b1c5ec

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
theorem cut_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex parent : Int) :
    FibonacciHeap.cut.Call heap (queue, vertex, parent)
      (cutHeap heap queue layout vertex parent) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  have finish (prepared : Heap) (state : State_FibonacciHeap_cut)
      (ready : layout.Valid prepared state.v0) :
      Reaches Step (.active prepared (.fn_FibonacciHeap_cut 12 state) stack)
        (resumeConfig (cutTailHeap prepared state.v0 layout state.v1 state.v2)
          (.fn_FibonacciHeap_cut ()) stack) := by
    let decreased := prepared.write layout.degrees state.v2
      (prepared.read layout.degrees state.v2 - 1)
    have decreasedValid : layout.Valid decreased state.v0 :=
      Layout.Valid.write _ _ _ ready _ _ _
    have detachedValid := remove_preserves_layout decreased state.v0 layout decreasedValid state.v1
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc12 _ _ _
      (by simp [ready.readDegrees, ready.degreesAllocated]))
    simp only [ready.readDegrees, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc11 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc10 _ _ _ ready.object)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc9 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc8 _ _ _)
    apply Reaches.trans ((remove_from_ring_summary decreased state.v0 layout
      decreasedValid state.v1).2 _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc7 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc6 _ _ _ detachedValid.object)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc5 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc4 _ _ _)
    apply Reaches.trans ((add_root_summary _ state.v0 layout detachedValid state.v1).2 _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc2 _ _ _)
    exact Reaches.single (Step.FibonacciHeap_cut_pc1 _ _ _)
  apply Reaches.prepend (Step.FibonacciHeap_cut_pc18 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  by_cases head : heap.read layout.children parent = vertex
  · apply Reaches.prepend (Step.FibonacciHeap_cut_pc17_true _ _ _
      (by simp [valid.readChildren, head]))
    apply Reaches.prepend (Step.FibonacciHeap_cut_pc16 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    by_cases singleton : heap.read layout.right vertex = vertex
    · apply Reaches.prepend (Step.FibonacciHeap_cut_pc15_true _ _ _
        (by simp [valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_cut_pc13 _ _ _
        (by simp [valid.readChildren, valid.childrenAllocated]))
      simp only [cutHeap, cutHeaderHeap, if_pos head, if_pos singleton,
        valid.readChildren, valid.readRight, Option.getD_some]
      apply finish
      exact Layout.Valid.write _ _ _ valid _ _ _
    · apply Reaches.prepend (Step.FibonacciHeap_cut_pc15_false _ _ _
        (by simp [valid.readRight, singleton]))
      apply Reaches.prepend (Step.FibonacciHeap_cut_pc14 _ _ _
        (by simp [valid.readRight, valid.rightAllocated, valid.readChildren,
          valid.childrenAllocated]))
      simp only [cutHeap, cutHeaderHeap, if_pos head, if_neg singleton,
        valid.readChildren, valid.readRight, Option.getD_some]
      apply finish
      exact Layout.Valid.write _ _ _ valid _ _ _
  · apply Reaches.prepend (Step.FibonacciHeap_cut_pc17_false _ _ _
      (by simp [valid.readChildren, head]))
    simp only [cutHeap, cutHeaderHeap, if_neg head, valid.readChildren, Option.getD_some]
    apply finish
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
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex parent : Int),
          Algo.fibonacci_heap.FibonacciHeap.cut.Call heap
            (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex parent))
            (FibonacciModuleAnalysis.cutHeap heap queue layout vertex parent) () :=
  FibonacciModuleAnalysis.cut_summary
