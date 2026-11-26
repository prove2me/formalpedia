-- Prove2me | solution 1 for BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:41.673016+00:00
-- url     : https://prove2.me/submissions/2bea22b1-e3bc-4276-80cd-6d39fe37b52c

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux


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
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ))
        MeasureTheory.volume 0 top) :
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
  rw [integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
    choices F e pref prefixTs top ρ hstd hrec]
  rw [integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux]
end BKAR.Forest
