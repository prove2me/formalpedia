-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:50.703652+00:00
-- url     : https://prove2.me/submissions/a0953999-29ea-43ad-ac96-fc7dae0ae77a

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_standard_intervalIntegrable
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_recursive_sum_intervalIntegrable
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum
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
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e.val]
        (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ ts)))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by
  exact
    integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum
      choices F e pref prefixTs top ρ
      (allBranchesAnalytic.child_standard_intervalIntegrable
        choices F e pref prefixTs top ρ hanalytic)
      (allBranchesAnalytic.child_recursive_sum_intervalIntegrable
        choices F e pref prefixTs top ρ hanalytic)
end BKAR.Forest
