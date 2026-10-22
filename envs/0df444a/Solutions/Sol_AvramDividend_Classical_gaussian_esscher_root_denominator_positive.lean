-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_root_denominator_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:14:38.556483+00:00
-- url     : https://prove2.me/submissions/25134065-2ce5-4405-a3aa-d78502da0265

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_quadratic_lower_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- Positive Gaussian variance and nonnegative Esscher drift
force a positive resolvent denominator. -/
theorem solution (μ : Measure ℝ) (b a q φ θ : ℝ)
    (ha : 0 < a) (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q)
    (hdrift : 0 ≤ b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) :
    0 < (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q := by
  have hquad : 0 < a * θ ^ 2 :=
    mul_pos ha (pow_pos hθ 2)
  have hlinear : 0 ≤ θ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) :=
    mul_nonneg hθ.le hdrift
  have hsum : 0 < θ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) + a * θ ^ 2 := by
    linarith
  have hbound :=
    gaussian_levy_esscher_shift_quadratic_lower_real μ b a φ θ
      hφ hθ.le hlevy
  rw [← hroot]
  exact lt_of_lt_of_le hsum hbound
