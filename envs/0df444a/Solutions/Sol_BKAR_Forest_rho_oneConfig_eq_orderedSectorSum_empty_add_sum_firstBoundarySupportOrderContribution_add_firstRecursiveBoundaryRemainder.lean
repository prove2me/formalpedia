-- Prove2me | solution 1 for BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_firstRecursiveBoundaryRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:55.574963+00:00
-- url     : https://prove2.me/submissions/ebd919eb-c7a6-4c3f-a3a3-08163de644c0

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_firstRecursiveBoundaryRemainder_def
import Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_sum_integral_child_sum

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              firstBoundarySupportOrderContribution choices I order ρ)) +
        firstRecursiveBoundaryRemainder choices ρ) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_sum_integral_child_sum
    choices ρ hanalytic]
  rw [firstRecursiveBoundaryRemainder_def]
end BKAR.Forest
