-- Prove2me | solution 1 for BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:42.120348+00:00
-- url     : https://prove2.me/submissions/5ab6ae8b-bbdf-45bc-b4d2-daa36e5bd953

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_def
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
import Theorems.Thm_BKAR_Forest_sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              localBoundarySupportOrderContribution choices F pref prefixTs
                top I order ρ)) +
          localRecursiveBoundaryRemainder choices F pref prefixTs top ρ) := by
  rw [allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum]
  rw [sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
    choices F pref prefixTs top ρ hpref hnodup hanalytic]
  rw [localRecursiveBoundaryRemainder_def]
end BKAR.Forest
