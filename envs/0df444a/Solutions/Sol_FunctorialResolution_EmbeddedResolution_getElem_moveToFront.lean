-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.getElem_moveToFront
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:38.530805+00:00
-- url     : https://prove2.me/submissions/32636523-c6bc-4b7a-b3bc-240e7271630c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexBeforeMoveToFront_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexBeforeMoveToFront_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < (moveToFront E j).length) :
    (moveToFront E j)[i]'hi =
      E[indexBeforeMoveToFront j i]'(indexBeforeMoveToFront_lt_length E j hj i (by
        rw [length_moveToFront E j hj] at hi; exact hi)) := by
  have hi' : i < E.length := by rw [length_moveToFront E j hj] at hi; exact hi
  have hlt : indexBeforeMoveToFront j i < E.length := indexBeforeMoveToFront_lt_length E j hj i hi'
  have key : (moveToFront E j)[i]? = E[indexBeforeMoveToFront j i]? := by
    rw [moveToFront_eq_cons E j hj]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, indexBeforeMoveToFront_zero, List.getElem?_eq_getElem hj]
    | succ m =>
      rw [List.getElem?_cons_succ, indexBeforeMoveToFront_succ]
      by_cases hm : m < j
      · rw [if_pos hm]
        simp [List.getElem?_eraseIdx_of_lt, hm]
      · rw [if_neg hm]
        have hm' : j ≤ m := by omega
        simp [List.getElem?_eraseIdx_of_ge, hm']
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hlt] at key
  exact Option.some.inj key
end FunctorialResolution.EmbeddedResolution
