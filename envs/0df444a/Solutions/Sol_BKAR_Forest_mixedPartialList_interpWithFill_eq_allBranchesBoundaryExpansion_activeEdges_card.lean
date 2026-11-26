-- Prove2me | solution 1 for BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:28.330841+00:00
-- url     : https://prove2.me/submissions/d9b80067-4978-41d5-b535-4aaa47a6c1a7

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_allBranchesExpansion
import Theorems.Thm_BKAR_Forest_allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
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
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by
  rw [← allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    choices F pref prefixTs top ρ]
  exact
    mixedPartialList_interpWithFill_eq_allBranchesExpansion
      choices F.activeEdges.card F pref prefixTs top ρ
      hpref hprefixTs hanalytic
end BKAR.Forest
