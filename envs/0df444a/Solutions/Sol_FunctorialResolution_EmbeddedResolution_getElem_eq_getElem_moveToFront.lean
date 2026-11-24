-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.getElem_eq_getElem_moveToFront
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:37.058029+00:00
-- url     : https://prove2.me/submissions/660a7e1e-0e88-4e4e-8893-4cf53e8f96ff

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_indexInMoveToFront_self

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
    (hi : i < E.length) :
    E[i]'hi = (moveToFront E j)[indexInMoveToFront j i]'(indexInMoveToFront_lt_length E j hj i hi) := by
  rcases lt_trichotomy i j with h | h | h
  · have hb : indexInMoveToFront j i = i + 1 := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_lt, h]
  · subst h
    simp only [moveToFront_eq_cons E _ hj, indexInMoveToFront_self, List.getElem_cons_zero]
  · have hb : indexInMoveToFront j i = i := by
      simp only [indexInMoveToFront]
      split_ifs <;> omega
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hjk : j ≤ k := by omega
    simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_ge, hjk]
end FunctorialResolution.EmbeddedResolution
