-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_root_resolvent_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:45:54.591858+00:00
-- url     : https://prove2.me/submissions/8eadc47f-642d-4f39-a429-18597379e627

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_tilted_drift
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_root_denominator_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- Every positive q-root gives a strictly positive Gaussian Esscher
resolvent denominator, with no additional drift-sign assumption. -/
theorem solution (μ : Measure ℝ) (b a q φ θ : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot : b * φ + a * φ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) - 1 +
          φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    0 < (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q := by
  have hdrift := gaussian_positive_root_tilted_drift
    μ b a q φ ha.le hq hφ hlevy hroot
  exact gaussian_esscher_root_denominator_positive
    μ b a q φ θ ha hφ hθ hlevy hroot hdrift.le
