-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_allBranchesBoundaryExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:57.190847+00:00
-- url     : https://prove2.me/submissions/0045a772-2574-40a6-8617-17bb10027bd7

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
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
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by
  rw [mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
    choices F pref prefixTs top ρ hpref hprefixTs hanalytic]
  rw [allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum]
end BKAR.Forest
