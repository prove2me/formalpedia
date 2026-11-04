-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_normalised_weight_exponential_image_moment_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:01:38.718757+00:00
-- url     : https://prove2.me/submissions/984a9556-1f5b-417f-9da5-aa7ee5527e59

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_lintegral_normalised_weight_mul
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ) (h : ℝ) :
    (∫⁻ ω, (ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
      (ENNReal.ofReal h)⁻¹) *
      (ENNReal.ofReal (Real.exp (θ * Y ω))) ^ k ∂μ) =
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) / ENNReal.ofReal h := by
  have hz : Measurable (fun ω => Real.exp (θ * Y ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul hY)
  have hw : Measurable (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hz.sub_const 1).pow_const 4)
  have hg : Measurable (fun ω =>
      (ENNReal.ofReal (Real.exp (θ * Y ω))) ^ k) :=
    (ENNReal.measurable_ofReal.comp hz).pow_const k
  have hpow :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
        (ENNReal.ofReal (Real.exp (θ * Y ω))) ^ k ∂μ) =
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k) ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    rw [ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _))]
  calc
    _ = (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
          (ENNReal.ofReal (Real.exp (θ * Y ω))) ^ k ∂μ) *
          (ENNReal.ofReal h)⁻¹ :=
      AvramDividend.Classical.avram_p2_b_rate_lintegral_normalised_weight_mul
        μ _ _ hw hg _
    _ = (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((μ.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * Y ω)))) * (ENNReal.ofReal h)⁻¹ := by
      rw [hpow]
      rw [AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
        μ Y hY θ k]
    _ = _ := by rw [div_eq_mul_inv]
