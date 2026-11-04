-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_integrable_weighted_image_kmoment_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:02:43.443367+00:00
-- url     : https://prove2.me/submissions/1e334b5f-2634-45ec-bb18-95b9b7579f46

import Mathlib.Tactic.Positivity
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (θ : ℝ) (k : ℕ)
    (hInt : Integrable (fun ω =>
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) < ⊤ := by
  have hz : Measurable (fun ω => Real.exp (θ * Y ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul hY)
  have hwreal : Measurable (fun ω =>
      (Real.exp (θ * Y ω) - 1) ^ 4) :=
    (hz.sub_const 1).pow_const 4
  have hw : Measurable (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp hwreal
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) := by fun_prop
  rw [AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
    μ Y hY θ k]
  have heq :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k) ∂μ) =
      (∫⁻ ω, ENNReal.ofReal
        ((Real.exp (θ * Y ω)) ^ k *
          (Real.exp (θ * Y ω) - 1) ^ 4) ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [heq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hInt (Filter.Eventually.of_forall (fun ω => by positivity))]
  exact ENNReal.ofReal_lt_top
