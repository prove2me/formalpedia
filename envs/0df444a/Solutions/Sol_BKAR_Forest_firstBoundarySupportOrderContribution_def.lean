-- Prove2me | solution 1 for BKAR.Forest.firstBoundarySupportOrderContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:14:51.699857+00:00
-- url     : https://prove2.me/submissions/f64f6987-cba0-4887-93eb-7a8468d07c05

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support = I ∧
              [e.val] = order))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution order ρ) := by
  rw [firstBoundarySupportOrderContribution]
end BKAR.Forest
