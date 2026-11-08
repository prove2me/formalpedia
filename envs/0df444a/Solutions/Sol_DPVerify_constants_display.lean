-- Prove2me | solution 1 for DPVerify.constants_display
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T14:56:52.502769+00:00
-- url     : https://prove2.me/submissions/9ade5720-936f-46c3-98fb-acd47dd49733

import Mathlib

/-- DPVerify §4: the constants display of the completeness and soundness bounds. -/
theorem solution (α t κ ρ : ℝ) (hα : α = 0.001) (ht : t = 6) (hκ : κ = 20)
    (hρ : ρ ≤ 1 / 10 ^ 4) :
    0.733 ≤ (1 - 1 / t - t * (α + ρ)) * (κ ^ 2 / (κ ^ 2 + t ^ 2)) -
      4 * κ * ρ * Real.pi ∧
    Real.pi * κ * (α + ρ) + 4 * κ * Real.pi * ρ ≤ 0.0943 := by
  subst hα
  subst ht
  subst hκ
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpil : Real.pi < 3.141593 := Real.pi_lt_d6
  constructor
  · by_cases hρ0 : 0 ≤ ρ
    · have hρpi : ρ * Real.pi ≤ 1 / 10 ^ 4 * 3.141593 :=
        mul_le_mul hρ hpil.le hpi0.le (by norm_num)
      nlinarith
    · have hρpi : ρ * Real.pi ≤ 0 :=
        le_of_lt (mul_neg_of_neg_of_pos (by linarith) hpi0)
      nlinarith
  · by_cases hρ0 : 0 ≤ ρ
    · have hρpi : ρ * Real.pi ≤ 1 / 10 ^ 4 * 3.141593 :=
        mul_le_mul hρ hpil.le hpi0.le (by norm_num)
      nlinarith
    · have hρpi : ρ * Real.pi ≤ 0 :=
        le_of_lt (mul_neg_of_neg_of_pos (by linarith) hpi0)
      nlinarith
