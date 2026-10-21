-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:57:19.261984+00:00
-- url     : https://prove2.me/submissions/db14b4a8-49c9-40ae-9561-05e00cbf1a16

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
Dominated convergence for upper-first passage discount expectations.
The remaining pathwise first-passage convergence is an explicit input;
the exact payoff, including both-infinite conventions, is unchanged.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q)
    (upGrid downGrid : ℕ → Ω → ℝ≥0∞)
    (up down : Ω → ℝ≥0∞)
    (hu : ∀ n, Measurable (upGrid n))
    (hd : ∀ n, Measurable (downGrid n))
    (hlim : ∀ᵐ ω ∂P,
      Tendsto
        (fun n => if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) atTop
        (𝓝 (if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0))) :
    Tendsto
      (fun n => ∫⁻ ω,
        if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0 ∂P)
      atTop
      (𝓝 (∫⁻ ω,
        if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P)) := by
  have hmeas (n : ℕ) : Measurable
      (fun ω : Ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) := by
    have htime : Measurable (fun ω : Ω =>
        ENNReal.toReal (upGrid n ω)) :=
      ENNReal.measurable_toReal.comp (hu n)
    have hpay : Measurable (fun ω : Ω =>
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n ω))))) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp
          ((measurable_const.mul htime).neg))
    exact Measurable.ite (measurableSet_lt (hu n) (hd n))
      hpay measurable_const
  have hbound (n : ℕ) :
      (fun ω : Ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) ≤ᵐ[P] (fun _ => (1 : ℝ≥0∞)) :=
    Filter.Eventually.of_forall (fun ω =>
      chat03_discounted_upperfirst_weight_le_one
        q hq (upGrid n ω) (downGrid n ω))
  exact tendsto_lintegral_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ≥0∞)) hmeas hbound
    (by simp) hlim
