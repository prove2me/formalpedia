-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_integrated_drift_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:33:52.024495+00:00
-- url     : https://prove2.me/submissions/17b0bec5-e4de-4c92-aacc-f6228ddca17d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_jump_drift_secant_bound
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_real_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_real_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The real jump exponent at a positive Esscher parameter is bounded
by that parameter times the absolutely integrable jump drift. -/
theorem solution (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫ z in Ioi (0 : ℝ),
      Real.exp (-φ * z) - 1 +
        φ * (if z ≤ 1 then z else 0) ∂μ) ≤
      φ * (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) -
          z * Real.exp (-φ * z) ∂μ) := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  have hJ := gaussian_levy_jump_real_integrable μ φ hφ.le hlevy
  have hD := gaussian_esscher_drift_real_integrable μ φ hφ hlevy
  change Integrable (fun z : ℝ =>
    Real.exp (-φ * z) - 1 +
      φ * (if z ≤ 1 then z else 0)) ν at hJ
  change Integrable (fun z : ℝ =>
    (if z ≤ 1 then z else 0) -
      z * Real.exp (-φ * z)) ν at hD
  have hscaled : Integrable (fun z : ℝ =>
      φ * ((if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z))) ν := hD.const_mul φ
  have hpoint (z : ℝ) :
      Real.exp (-φ * z) - 1 +
        φ * (if z ≤ 1 then z else 0) ≤
      φ * ((if z ≤ 1 then z else 0) -
        z * Real.exp (-φ * z)) :=
    gaussian_esscher_jump_drift_secant_bound φ z _
  change (∫ z : ℝ, Real.exp (-φ * z) - 1 +
      φ * (if z ≤ 1 then z else 0) ∂ν) ≤
    φ * (∫ z : ℝ, (if z ≤ 1 then z else 0) -
      z * Real.exp (-φ * z) ∂ν)
  calc
    _ ≤ ∫ z : ℝ, φ * ((if z ≤ 1 then z else 0) -
      z * Real.exp (-φ * z)) ∂ν :=
      integral_mono hJ hscaled hpoint
    _ = _ := integral_const_mul _ _
