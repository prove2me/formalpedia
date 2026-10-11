-- Prove2me | solution 1 for FibonacciModuleAnalysis.add_root_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:27.942919+00:00
-- url     : https://prove2.me/submissions/477ff42d-3b3d-4fa2-a721-7c3b0ce4a025

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
































































theorem add_root_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (vertex : Int) :
    FibonacciHeap.add_root.Call heap (queue, vertex)
      (addRootHeap heap queue layout vertex) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc19 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc18 _ _ _
    (by simp [valid.readMarks, valid.marksAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_add_root_pc17 _ _ _
    (by simp [valid.readMinimum]))
  simp only [marks_write, minimum_write, valid.readParents, valid.readMarks, valid.readMinimum, Option.getD_some]
  by_cases empty : layout.minimum < 0
  · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc16_true _ _ _
      (by simp [empty]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc5 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc4 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc3 _ _ _ valid.object)
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
    simpa only [addRootHeap, if_pos empty, rootHeaderHeap, left_write, right_write,
      parents_write, marks_write, valid.readParents, valid.readMarks, valid.readLeft,
      valid.readRight, Option.getD_some] using
      (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))
  · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc16_false _ _ _
      (by simp [empty]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc15 _ _ _
      (by simp [valid.readMinimum]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc14 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    simp only [minimum_write, right_write, valid.readMinimum, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc13 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc12 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc11 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc10 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc9 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_add_root_pc8 _ _ _
      (by simp [valid.readKeys, valid.keysAllocated]))
    simp only [keys_write, keys_tick, valid.readKeys, Option.getD_some]
    let linked := (insertRingHeap (rootHeaderHeap heap layout vertex) layout vertex).tick
      "heap_comparisons"
    by_cases smaller : linked.read layout.keys vertex < linked.read layout.keys layout.minimum
    · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc7_true _ _ _
        (by simpa [linked, insertRingHeap, rootHeaderHeap, valid.readParents,
          valid.readMarks, valid.readLeft, valid.readRight, valid.readKeys,
          valid.readMinimum] using smaller))
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc6 _ _ _ valid.object)
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
      have effect : addRootHeap heap queue layout vertex =
          set_FibonacciHeap_minimum linked queue vertex := by
        unfold addRootHeap
        rw [if_neg empty]
        exact if_pos smaller
      rw [effect]
      simpa only [linked, insertRingHeap,
        rootHeaderHeap, left_write, right_write, parents_write, marks_write,
        minimum_write, valid.readParents, valid.readMarks, valid.readLeft,
        valid.readRight, valid.readMinimum, Option.getD_some] using
        (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))
    · apply Reaches.prepend (Step.FibonacciHeap_add_root_pc7_false _ _ _
        (by simpa [linked, insertRingHeap, rootHeaderHeap, valid.readParents,
          valid.readMarks, valid.readLeft, valid.readRight, valid.readKeys,
          valid.readMinimum] using smaller))
      apply Reaches.prepend (Step.FibonacciHeap_add_root_pc2 _ _ _)
      have effect : addRootHeap heap queue layout vertex = linked := by
        unfold addRootHeap
        rw [if_neg empty]
        exact if_neg smaller
      rw [effect]
      simpa only [linked, insertRingHeap,
        rootHeaderHeap, left_write, right_write, parents_write, marks_write,
        minimum_write, valid.readParents, valid.readMarks, valid.readLeft,
        valid.readRight, valid.readMinimum, Option.getD_some] using
        (Reaches.single (Step.FibonacciHeap_add_root_pc1 _ _ _))















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
        ∀ (vertex : Int),
          Algo.fibonacci_heap.FibonacciHeap.add_root.Call heap (Prod.mk.{0, 0} queue vertex)
            (FibonacciModuleAnalysis.addRootHeap heap queue layout vertex) () :=
  FibonacciModuleAnalysis.add_root_summary
