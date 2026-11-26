-- Prove2me | solution 1 for BKAR.Forest.sum_firstBoundarySupportOrderContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:42.108094+00:00
-- url     : https://prove2.me/submissions/a6b0c31c-aa91-49a9-968e-1a81edbf5f56

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_sum_firstBoundarySupportContribution
import Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_eq_sum_supportOrderContribution

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            firstBoundarySupportOrderContribution choices I order ρ)) := by
  rw [sum_firstBoundarySupportContribution choices ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [firstBoundarySupportContribution_eq_sum_supportOrderContribution
    choices I ρ]
end BKAR.Forest
