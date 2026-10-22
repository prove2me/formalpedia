-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_jump_truncation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:31:49.441692+00:00
-- url     : https://prove2.me/submissions/cb19160f-df94-486b-8bfe-3f9a6d9b1178

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Canonical Lévy truncation bounds the negative exponential jump term. -/
theorem solution (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    |Real.exp (-θ * z) - 1 + θ * (if z ≤ 1 then z else 0)| ≤
      (1 + θ ^ 2) * min 1 (z ^ 2) := by
  by_cases hsmall : z ≤ 1
  · have hc :=
      gaussian_compensated_jump_pos_linear θ z hθ hz
    have hq :=
      gaussian_compensated_jump_quadratic θ z hθ hz
    have hzsq : z ^ 2 ≤ (1 : ℝ) := by nlinarith
    rw [if_pos hsmall, min_eq_right hzsq]
    rw [abs_of_nonneg hc.1]
    nlinarith [sq_nonneg z]
  · have hlarge : 1 < z := lt_of_not_ge hsmall
    have hnonpos : -θ * z ≤ 0 := by nlinarith
    have he : 0 < Real.exp (-θ * z) := Real.exp_pos _
    have hle : Real.exp (-θ * z) ≤ 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr hnonpos)
    have hzsq : (1 : ℝ) ≤ z ^ 2 := by nlinarith
    rw [if_neg hsmall, min_eq_left hzsq]
    simp only [mul_zero, add_zero, mul_one]
    rw [abs_of_nonpos (by linarith : Real.exp (-θ * z) - 1 ≤ 0)]
    nlinarith [sq_nonneg θ]
