-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_esscher_shift_quadratic_lower_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:08:59.188915+00:00
-- url     : https://prove2.me/submissions/9dd97650-ec8d-4949-b9d0-a19c97d6898e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_real
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- Nonnegative compensated jumps give a sharp lower bound on the full real exponent shift. -/
theorem solution (μ : Measure ℝ) (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    θ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) +
      a * θ ^ 2 ≤
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) -
      (b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ)) := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hCnn : ∀ᵐ z : ℝ ∂ν,
      0 ≤ Real.exp (-φ * z) *
        (Real.exp (-θ * z) - 1 + θ * z) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (gaussian_compensated_jump_pos_linear θ z hθ hz.le).1
  have hCbound :
      0 ≤ ∫ z : ℝ, Real.exp (-φ * z) *
        (Real.exp (-θ * z) - 1 + θ * z) ∂ν :=
    integral_nonneg_of_ae hCnn
  have hshift :=
    gaussian_levy_esscher_shift_real μ b a φ θ hφ hθ hlevy
  rw [hshift]
  simpa only [ν, add_zero] using
    add_le_add_right hCbound
      (θ * (b + 2 * a * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) -
            z * Real.exp (-φ * z) ∂μ)) + a * θ ^ 2)
