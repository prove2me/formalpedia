-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_root_volterra_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:11:15.752825+00:00
-- url     : https://prove2.me/submissions/0638747f-ceb6-4283-a8ba-f7be72951ee9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_volterra_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Exact q-resolvent denominator after centring at a positive Esscher root. -/
theorem solution (μ : Measure ℝ) [SFinite μ] (b a q φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hroot :
      b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ) = q) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) - q =
      θ * (b + 2 * a * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) -
            z * Real.exp (-φ * z) ∂μ)) +
        a * θ ^ 2 +
        θ ^ 2 *
          (∫⁻ t : ℝ, ∫⁻ z : ℝ,
            (if 0 < t ∧ t < z then
              ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
                ENNReal.ofReal (Real.exp (-φ * z))
             else 0) ∂μ ∂volume).toReal := by
  rw [← hroot]
  exact gaussian_levy_esscher_volterra_real
    μ b a φ θ hφ hθ hlevy
