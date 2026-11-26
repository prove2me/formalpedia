-- Prove2me | solution 1 for BKAR.Forest.integral_mixedPartialList_cons_interpWithFill_eq_integral_child_standard_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:31.845421+00:00
-- url     : https://prove2.me/submissions/f9466b4c-d707-437c-b2f1-ce1de2bcbcc7

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_integral_mixedPartialList_cons_interpWithFill_eq_integral_allBranchesBoundaryExpansion_child
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
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
        (mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t]))) +
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
  rw [integral_mixedPartialList_cons_interpWithFill_eq_integral_allBranchesBoundaryExpansion_child
    choices F e pref prefixTs hpref hprefixTs top ρ hanalytic]
  exact
    integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
      choices F e pref prefixTs top ρ
end BKAR.Forest
