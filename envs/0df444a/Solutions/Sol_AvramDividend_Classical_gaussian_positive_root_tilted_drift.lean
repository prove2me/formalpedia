-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_root_tilted_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:42:20.140336+00:00
-- url     : https://prove2.me/submissions/a7f8fda3-a05e-41c6-b486-8fdc6dbc02de

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_integrated_drift_secant_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- Any positive Esscher q-root forces a positive Gaussian-corrected
tilted drift when the Gaussian quadratic coefficient is nonnegative. -/
theorem solution (μ : Measure ℝ) (b a q φ : ℝ)
    (ha : 0 ≤ a) (hq : 0 < q) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    0 < b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ) := by
  have hJ := gaussian_esscher_integrated_drift_secant_bound
    μ φ hφ hlevy
  have hGauss : 0 ≤ a * φ ^ 2 :=
    mul_nonneg ha (sq_nonneg φ)
  have hsecant : q ≤ φ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) := by
    rw [← hroot]
    nlinarith
  have hpositive : 0 < φ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) := lt_of_lt_of_le hq hsecant
  by_contra hnot
  have hle : b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ) ≤ 0 := le_of_not_gt hnot
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hφ.le hle
  linarith
