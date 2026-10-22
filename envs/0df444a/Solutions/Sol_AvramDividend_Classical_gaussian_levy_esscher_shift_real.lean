-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_esscher_shift_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:43:16.421265+00:00
-- url     : https://prove2.me/submissions/60ca0abb-85cb-44cd-9cee-5e9ca7508125

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_jump_integral_shift
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_real_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_real_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_real_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- Gaussian Lévy–Khintchine exponent shift with the genuine canonical jump integrals. -/
theorem solution (μ : Measure ℝ) (b a φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
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
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-φ * z) *
              (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let J : ℝ → ℝ := fun u =>
    ∫ z : ℝ, Real.exp (-u * z) - 1 +
      u * (if z ≤ 1 then z else 0) ∂ν
  let C : ℝ := ∫ z : ℝ,
    Real.exp (-φ * z) *
      (Real.exp (-θ * z) - 1 + θ * z) ∂ν
  let D : ℝ := ∫ z : ℝ,
    (if z ≤ 1 then z else 0) -
      z * Real.exp (-φ * z) ∂ν
  have hA :=
    gaussian_levy_jump_real_integrable μ (φ + θ)
      (add_nonneg hφ.le hθ) hlevy
  have hB :=
    gaussian_levy_jump_real_integrable μ φ hφ.le hlevy
  have hC :=
    gaussian_shifted_compensator_real_integrable μ φ θ hφ hθ hlevy
  have hD :=
    gaussian_esscher_drift_real_integrable μ φ hφ hlevy
  have hshift : J (φ + θ) - J φ = C + θ * D := by
    simpa only [J, C, D] using
      (gaussian_esscher_jump_integral_shift ν φ θ
        (fun z => if z ≤ 1 then z else 0) hA hB hC hD)
  change (b * (φ + θ) + a * (φ + θ) ^ 2 + J (φ + θ)) -
    (b * φ + a * φ ^ 2 + J φ) =
      θ * (b + 2 * a * φ + D) + a * θ ^ 2 + C
  calc
    _ = (b * (φ + θ) + a * (φ + θ) ^ 2) -
      (b * φ + a * φ ^ 2) + (J (φ + θ) - J φ) := by ring
    _ = (b * (φ + θ) + a * (φ + θ) ^ 2) -
      (b * φ + a * φ ^ 2) + (C + θ * D) := by rw [hshift]
    _ = _ := by ring
