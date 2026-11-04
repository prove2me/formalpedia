-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_polynomial_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:57:14.53698+00:00
-- url     : https://prove2.me/submissions/af84e18f-88e9-4823-8c76-44351b30807b

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (w : Ω → ℝ≥0∞) (hw : Measurable w) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k
      ∂((μ.withDensity w).map (fun ω => Real.exp (Y ω)))) =
    ∫⁻ ω, w ω * (ENNReal.ofReal (Real.exp (Y ω))) ^ k ∂μ := by
  have hpow : Measurable (fun z : ℝ => (ENNReal.ofReal z) ^ k) := by
    fun_prop
  have hexp : Measurable (fun ω => Real.exp (Y ω)) := by
    fun_prop
  have hcomp : Measurable
      (fun ω => (ENNReal.ofReal (Real.exp (Y ω))) ^ k) := by
    fun_prop
  calc
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k
        ∂((μ.withDensity w).map (fun ω => Real.exp (Y ω)))) =
        ∫⁻ ω, (ENNReal.ofReal (Real.exp (Y ω))) ^ k
          ∂(μ.withDensity w) := by
      exact lintegral_map hpow hexp
    _ = ∫⁻ ω, w ω * (ENNReal.ofReal (Real.exp (Y ω))) ^ k ∂μ := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul μ hw hcomp)
