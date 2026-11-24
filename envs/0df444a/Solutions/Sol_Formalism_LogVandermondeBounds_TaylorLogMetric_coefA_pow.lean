-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.TaylorLogMetric.coefA_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:42.708291+00:00
-- url     : https://prove2.me/submissions/28faf9a3-4c73-44af-9ccd-2fa5b56dd571

import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_sq_ge_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.TaylorLogMetric
open Finset
namespace Formalism.LogVandermondeBounds.TaylorLogMetric
theorem _root_.solution (p i j : ℕ) (hp : 2 ≤ p) :
    coefA p ((p ^ 2) ^ i) (p * (p ^ 2) ^ j) = if i ≤ j then 1 / (p : ℚ) ^ (i + j + 1) else 0 := by
  unfold coefA
  by_cases hij : i ≤ j
  · have h : ∃ i' j', i' ≤ j' ∧ (p ^ 2) ^ i = (p ^ 2) ^ i' ∧ p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' :=
      ⟨i, j, hij, rfl, rfl⟩
    rw [dif_pos h, if_pos hij]
    obtain ⟨-, h2, h3⟩ := Classical.choose_spec (Classical.choose_spec h)
    have hi : i = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = Classical.choose (Classical.choose_spec h) :=
      Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    rw [← hj, ← hi]
  · rw [if_neg hij, dif_neg]
    rintro ⟨i', j', h1, h2, h3⟩
    have hi : i = i' := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = j' := Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    subst hi hj
    exact hij h1
end Formalism.LogVandermondeBounds.TaylorLogMetric
