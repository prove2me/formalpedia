-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.multinomial_le_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:45.254926+00:00
-- url     : https://prove2.me/submissions/c602fd62-72f6-4e4b-8c6a-fb2e306f9e5d

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution : MultinomialPowerBound := by
  intro k α
  have h1 : Nat.multinomial univ α ≤ k ^ (∑ i, α i) := by
    have key := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin k)) (fun _ => (1:ℕ))
      (∑ i, α i)
    simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at key
    rw [key]
    exact Finset.single_le_sum (f := fun β => Nat.multinomial univ β)
      (fun _ _ => Nat.zero_le _) (by simp [mem_piAntidiag])
  have hspec := Nat.multinomial_spec univ α
  have hpos : (0:ℝ) < ∏ i, ((α i).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hpos]
  calc ((∑ i, α i).factorial : ℝ) = (∏ i, ((α i).factorial : ℝ)) * Nat.multinomial univ α := by
        exact_mod_cast hspec.symm
    _ ≤ (∏ i, ((α i).factorial : ℝ)) * (k : ℝ) ^ (∑ i, α i) := by
        gcongr
        exact_mod_cast h1
    _ = _ := by ring
end Formalism.LogVandermondeBounds.flipTwoThree
