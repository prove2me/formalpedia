-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_k_exp_image_ofReal_pow_lintegrals_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:22:11.189235+00:00
-- url     : https://prove2.me/submissions/86f6ea0b-5e18-497f-8392-3bed0b51d20b

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On an exponential pushforward, taking the nonnegative lower part
before or after a natural power yields identical ENNReal moments. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Y : α → ℝ) (hY : Measurable Y) (k : ℕ) :
    (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
      μ.map (fun ω => Real.exp (Y ω))) =
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      μ.map (fun ω => Real.exp (Y ω))) := by
  have hG : Measurable (fun ω : α => Real.exp (Y ω)) :=
    (Real.measurable_exp).comp hY
  have hf1 : Measurable (fun z : ℝ => (ENNReal.ofReal z) ^ k) :=
    ENNReal.measurable_ofReal.pow_const k
  have hf2 : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const k)
  rw [lintegral_map hf1 hG, lintegral_map hf2 hG]
  apply lintegral_congr_ae
  filter_upwards [] with ω
  exact (ENNReal.ofReal_pow (le_of_lt (Real.exp_pos (Y ω))) k).symm
