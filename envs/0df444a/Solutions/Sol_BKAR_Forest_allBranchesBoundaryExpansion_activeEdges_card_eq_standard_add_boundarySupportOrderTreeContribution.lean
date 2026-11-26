-- Prove2me | solution 1 for BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_boundarySupportOrderTreeContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:33.810888+00:00
-- url     : https://prove2.me/submissions/9e6421e4-7632-4f2a-a2a0-94bfc9dcd6a5

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_def
import Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


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
        boundarySupportOrderTreeContribution choices F pref prefixTs top ρ := by
  rw [
    allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
      choices F pref prefixTs top ρ hpref hnodup hanalytic]
  have hfold :=
    localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
      choices F.activeEdges.card F pref prefixTs top ρ le_rfl hpref hnodup
      hanalytic
  rw [hfold]
  rw [boundarySupportOrderTreeContribution_def choices F pref prefixTs top ρ]
  rw [localBoundarySupportOrderSum_def]
end BKAR.Forest
