-- Prove2me | solution 2 for AvramDividend.Classical.countable_future_twoSided_discount_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:33:51.763922+00:00
-- url     : https://prove2.me/submissions/14d85fa5-ec59-46aa-8953-6b9082c4cd1c

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_exit_clocks_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (τ : ℕ → ℝ≥0) (q upper lower : ℝ) :
    Measurable (fun g : ℝ≥0 → ℝ =>
      let ρ : ℝ≥0∞ :=
        ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
      let σ : ℝ≥0∞ :=
        ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
      if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by
  obtain ⟨h1, h2⟩ := AvramDividend.Classical.countable_future_twoSided_exit_clocks_measurable τ upper lower
  refine Measurable.ite (measurableSet_lt h1 h2) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul (ENNReal.measurable_toReal.comp h1)).neg))
