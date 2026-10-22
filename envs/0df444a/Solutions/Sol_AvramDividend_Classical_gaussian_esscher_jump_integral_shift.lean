-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_jump_integral_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:22:08.286675+00:00
-- url     : https://prove2.me/submissions/c0ff685d-d8cb-49f8-a2d0-b3215eb99c5d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_algebra

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical

/-- Integrate the exact Esscher-shift jump identity when all four real terms are integrable. -/
theorem solution (μ : Measure ℝ) (φ θ : ℝ) (k : ℝ → ℝ)
    (hA : Integrable
      (fun z : ℝ => Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k z) μ)
    (hB : Integrable
      (fun z : ℝ => Real.exp (-φ * z) - 1 + φ * k z) μ)
    (hC : Integrable
      (fun z : ℝ =>
        Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) μ)
    (hD : Integrable
      (fun z : ℝ => k z - z * Real.exp (-φ * z)) μ) :
    (∫ z : ℝ, Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k z ∂μ) -
      (∫ z : ℝ, Real.exp (-φ * z) - 1 + φ * k z ∂μ) =
      (∫ z : ℝ,
        Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ∂μ) +
      θ * (∫ z : ℝ, k z - z * Real.exp (-φ * z) ∂μ) := by
  calc
    _ = (∫ z : ℝ,
      (Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k z) -
        (Real.exp (-φ * z) - 1 + φ * k z) ∂μ) :=
      (integral_sub hA hB).symm
    _ = (∫ z : ℝ,
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) +
        θ * (k z - z * Real.exp (-φ * z)) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun z => gaussian_levy_esscher_shift_algebra φ θ z (k z))
    _ = (∫ z : ℝ,
          Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ∂μ) +
        (∫ z : ℝ, θ * (k z - z * Real.exp (-φ * z)) ∂μ) :=
      integral_add hC (hD.const_mul θ)
    _ = _ := by rw [integral_const_mul]
