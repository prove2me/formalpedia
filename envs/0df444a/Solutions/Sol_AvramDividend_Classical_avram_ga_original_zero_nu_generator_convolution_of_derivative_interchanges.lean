-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_zero_nu_generator_convolution_of_derivative_interchanges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:55:15.551766+00:00
-- url     : https://prove2.me/submissions/9060286d-4a1d-4cb1-b6fa-23544f5cad07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_zero_nu_original_generator_exact
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (μ : Measure ℝ) (φ V : ℝ → ℝ) (ε y : ℝ)
    (hSecondI : Integrable
      (fun z => φ z * iteratedDeriv 2 V (y - ε*z)) μ)
    (hFirstI : Integrable
      (fun z => φ z * deriv V (y - ε*z)) μ)
    (hDeriv : deriv (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      ∫ z, φ z * deriv V (y - ε*z) ∂μ)
    (hSecond : iteratedDeriv 2
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      ∫ z, φ z * iteratedDeriv 2 V (y - ε*z) ∂μ) :
    X.generator (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      ∫ z, φ z * X.generator V (y - ε*z) ∂μ := by
  let K : ℝ → ℝ := fun t => ∫ z, φ z * V (t - ε*z) ∂μ
  have hGenK := (avram_gbB30_zero_nu_original_generator_exact X hν K y).2
  have hGenV (z : ℝ) :=
    (avram_gbB30_zero_nu_original_generator_exact X hν V (y - ε*z)).2
  have hS : Integrable
      (fun z => X.σ ^ 2 / 2 * (φ z * iteratedDeriv 2 V (y - ε*z))) μ :=
    hSecondI.const_mul _
  have hF : Integrable (fun z => X.c * (φ z * deriv V (y - ε*z))) μ :=
    hFirstI.const_mul _
  calc
    X.generator K y =
        X.σ ^ 2 / 2 * iteratedDeriv 2 K y + X.c * deriv K y := hGenK
    _ = X.σ ^ 2 / 2 * (∫ z, φ z * iteratedDeriv 2 V (y - ε*z) ∂μ) +
        X.c * (∫ z, φ z * deriv V (y - ε*z) ∂μ) := by rw [hDeriv, hSecond]
    _ = ∫ z, X.σ ^ 2 / 2 * (φ z * iteratedDeriv 2 V (y - ε*z)) +
        X.c * (φ z * deriv V (y - ε*z)) ∂μ := by
      rw [integral_add hS hF, integral_const_mul, integral_const_mul]
    _ = ∫ z, φ z * X.generator V (y - ε*z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hGenV z]
      ring
