-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:28.72384+00:00
-- url     : https://prove2.me/submissions/0db4bf5b-6ba1-46c1-a330-c107f1f51091

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
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
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
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
  apply intervalIntegral.integral_congr
  intro t _
  exact
    allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
      choices (choices F e).forest (pref ++ [e.val])
      (prefixTs ++ [t]) t ρ
end BKAR.Forest
