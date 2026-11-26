-- Prove2me | solution 1 for BKAR.Forest.integral_mixedPartialList_cons_interpWithFill_eq_integral_allBranchesBoundaryExpansion_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:29.336795+00:00
-- url     : https://prove2.me/submissions/8dc66f4e-009d-4cb5-823f-51653d2c1c98

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        mixedPartialList (e.val :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) =
      ∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact
    mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
      choices F e pref prefixTs hpref hprefixTs top ρ hanalytic ht
end BKAR.Forest
