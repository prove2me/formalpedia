-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:34:35.092911+00:00
-- url     : https://prove2.me/submissions/6f79dddc-8568-446f-af15-4e87ed79368a

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) =
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) *
      ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k) ∂μ := by
  have hz : Measurable (fun ω => Real.exp (θ * Y ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul hY)
  have hwreal : Measurable (fun ω =>
      (Real.exp (θ * Y ω) - 1) ^ 4) :=
    (hz.sub_const 1).pow_const 4
  have hw : Measurable (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp hwreal
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) := by fun_prop
  rw [MeasureTheory.lintegral_map hf hz]
  exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul μ hw (hf.comp hz)
