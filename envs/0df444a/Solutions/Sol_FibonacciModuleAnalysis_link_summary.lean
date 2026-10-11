-- Prove2me | solution 1 for FibonacciModuleAnalysis.link_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:43.491631+00:00
-- url     : https://prove2.me/submissions/f9ec962e-acf5-42e5-9640-3df1338517dc

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
theorem link_summary (heap : Heap) (queue : Ref_FibonacciHeap) (layout : Layout)
    (valid : layout.Valid heap queue) (child parent : Int) :
    FibonacciHeap.link.Call heap (queue, child, parent)
      (linkHeap heap layout child parent) () := by
  refine ⟨valid.object, ?_⟩
  intro stack
  apply Reaches.prepend (Step.FibonacciHeap_link_pc17 _ _ _
    (by simp [valid.readParents, valid.parentsAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc16 _ _ _
    (by simp [valid.readMarks, valid.marksAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc15 _ _ _
    (by simp [valid.readChildren, valid.childrenAllocated]))
  apply Reaches.prepend (Step.FibonacciHeap_link_pc14 _ _ _)
  simp only [marks_write, children_write, valid.readParents, valid.readMarks,
    valid.readChildren, Option.getD_some]
  by_cases empty : (linkHeaderHeap heap layout child parent).read layout.children parent < 0
  · apply Reaches.prepend (Step.FibonacciHeap_link_pc13_true _ _ _
      (by simpa [linkHeaderHeap] using empty))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc7 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc6 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc5 _ _ _
      (by simp [valid.readChildren, valid.childrenAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc4 _ _ _
      (by simp [valid.readDegrees, valid.degreesAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_link_pc2 _ _ _)
    simp only [linkHeap, linkRingHeap, linkHeaderHeap,
      left_write, right_write, children_write, degrees_write, valid.readLeft,
      valid.readRight, valid.readChildren, valid.readDegrees, Option.getD_some]
    simp only [linkHeaderHeap] at empty
    rw [if_pos empty]
    exact Reaches.single (Step.FibonacciHeap_link_pc1 _ _ _)
  · apply Reaches.prepend (Step.FibonacciHeap_link_pc13_false _ _ _
      (by simpa [linkHeaderHeap] using empty))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc12 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc11 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc10 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc9 _ _ _
      (by simp [valid.readRight, valid.rightAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc8 _ _ _
      (by simp [valid.readLeft, valid.leftAllocated]))
    simp only [left_write, right_write, valid.readLeft, valid.readRight, Option.getD_some]
    apply Reaches.prepend (Step.FibonacciHeap_link_pc5 _ _ _
      (by simp [valid.readChildren, valid.childrenAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc4 _ _ _
      (by simp [valid.readDegrees, valid.degreesAllocated]))
    apply Reaches.prepend (Step.FibonacciHeap_link_pc3 _ _ _)
    apply Reaches.prepend (Step.FibonacciHeap_link_pc2 _ _ _)
    simp only [linkHeap, linkRingHeap, linkHeaderHeap,
      children_write, degrees_write, valid.readChildren, valid.readDegrees, Option.getD_some]
    simp only [linkHeaderHeap] at empty
    rw [if_neg empty]
    exact Reaches.single (Step.FibonacciHeap_link_pc1 _ _ _)














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
        ∀ (child parent : Int),
          Algo.fibonacci_heap.FibonacciHeap.link.Call heap
            (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} child parent))
            (FibonacciModuleAnalysis.linkHeap heap layout child parent) () :=
  FibonacciModuleAnalysis.link_summary
