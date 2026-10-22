-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_esscher_volterra_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:01:22.407158+00:00
-- url     : https://prove2.me/submissions/28ad0968-57d9-4247-b250-6414c3ae0ee8

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_real
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_laplace_real_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Canonical Esscher exponent shift as a genuine
Gaussian double-tail Laplace transform. -/
theorem solution (μ : Measure ℝ) [SFinite μ] (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 < θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-(φ + θ) * z) - 1 +
          (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) -
      (b * φ + a * φ ^ 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-φ * z) - 1 +
            φ * (if z ≤ 1 then z else 0) ∂μ)) =
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
  have hshift :=
    gaussian_levy_esscher_shift_real μ b a φ θ hφ hθ.le hlevy
  have hLap :=
    gaussian_double_tail_laplace_real_bridge μ φ θ hφ hθ hlevy
  calc
    _ = θ * (b + 2 * a * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ)) +
        a * θ ^ 2 +
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-φ * z) *
              (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := hshift
    _ = _ := by rw [← hLap]
