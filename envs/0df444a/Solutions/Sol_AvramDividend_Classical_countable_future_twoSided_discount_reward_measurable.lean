-- Prove2me | solution 1 for AvramDividend.Classical.countable_future_twoSided_discount_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:33:27.940749+00:00
-- url     : https://prove2.me/submissions/1203b2df-ea8e-40ed-8c5e-3fe1c3a17c96

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_exit_clocks_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-! Discounted upper-before-lower exit reward on the full future-path space. -/
theorem solution
    (τ : ℕ → ℝ≥0) (q upper lower : ℝ) :
    Measurable (fun g : ℝ≥0 → ℝ =>
      let ρ : ℝ≥0∞ :=
        ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
      let σ : ℝ≥0∞ :=
        ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
      if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by
  classical
  let up : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun g => ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
  let down : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun g => ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
  obtain ⟨hup, hdown⟩ :=
    AvramDividend.Classical.countable_future_twoSided_exit_clocks_measurable τ upper lower
  have hEvent : MeasurableSet {g : ℝ≥0 → ℝ | up g < down g} :=
    measurableSet_lt hup hdown
  have hTime : Measurable (fun g : ℝ≥0 → ℝ => (up g).toReal) :=
    ENNReal.measurable_toReal.comp hup
  have hExp : Measurable (fun g : ℝ≥0 → ℝ =>
      Real.exp (-(q * (up g).toReal))) :=
    Real.measurable_exp.comp ((measurable_const.mul hTime).neg)
  have hPay : Measurable (fun g : ℝ≥0 → ℝ =>
      ENNReal.ofReal (Real.exp (-(q * (up g).toReal)))) :=
    ENNReal.measurable_ofReal.comp hExp
  change Measurable (fun g : ℝ≥0 → ℝ =>
    if up g < down g then
      ENNReal.ofReal (Real.exp (-(q * (up g).toReal))) else 0)
  exact Measurable.ite hEvent hPay measurable_const
