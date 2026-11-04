-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_original_normalized_weighted_image_kmoment_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:13:45.779043+00:00
-- url     : https://prove2.me/submissions/c705b4f1-fa4b-4958-9ebe-e11777b7712e

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_weighted_exp_polynomial_moments_finite
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- All positive-time, inverse-time-scaled original weighted exponential
image measures have finite ENNReal kth monomial moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      ((ENNReal.ofReal h)⁻¹ •
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω))))) < ⊤ := by
  let t := Real.toNNReal h
  let μ : Measure ℝ :=
    ((P.withDensity (fun ω => ENNReal.ofReal
      ((Real.exp (X.X t ω) - 1) ^ 4))).map
      (fun ω => Real.exp (X.X t ω)))
  have hXm : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hG : Measurable (fun ω : Ω => Real.exp (X.X t ω)) :=
    Real.measurable_exp.comp hXm
  have hw : Measurable (fun ω : Ω =>
      ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hG.sub_const 1).pow_const 4)
  have hf : Measurable (fun z : ℝ => (ENNReal.ofReal z) ^ k) :=
    ENNReal.measurable_ofReal.pow_const k
  have heq :
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
        (ENNReal.ofReal (Real.exp (X.X t ω))) ^ k ∂P) := by
    calc
      _ = ∫⁻ ω, (ENNReal.ofReal (Real.exp (X.X t ω))) ^ k ∂
          (P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X t ω) - 1) ^ 4))) := by
        exact lintegral_map hf hG
      _ = _ := by
        simpa only [Pi.mul_apply, Function.comp_apply] using
          (lintegral_withDensity_eq_lintegral_mul P hw (hf.comp hG))
  have hsource :=
    avram_p2_original_fourth_weighted_exp_polynomial_moments_finite X t k
  have hmoment : (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) < ⊤ := by
    rw [heq]
    have hsame :
        (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
          (ENNReal.ofReal (Real.exp (X.X t ω))) ^ k ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((Real.exp (X.X t ω) - 1) ^ 4) *
          ENNReal.ofReal ((Real.exp (X.X t ω)) ^ k) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      rw [← ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _)) k]
    rw [hsame]
    exact hsource
  have hPos : ENNReal.ofReal h ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hh).ne'
  have hInv : (ENNReal.ofReal h)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hPos)
  change (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂((ENNReal.ofReal h)⁻¹ • μ)) < ⊤
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top hInv hmoment
