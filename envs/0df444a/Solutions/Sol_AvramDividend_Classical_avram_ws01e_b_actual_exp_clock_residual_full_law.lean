-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_residual_full_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T01:00:37.872814+00:00
-- url     : https://prove2.me/submissions/75dbba3a-b07f-43b6-957b-3a494ad235fd

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exponential_nnreal_survival_memorylessness
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (p : ℝ) (hp : 0 < p)
    (hPos : (P.prod (expMeasure p))
      {z : Ω × ℝ | τ z.1 < z.2.toNNReal} ≠ 0) :
    Measure.map (fun z : Ω × ℝ =>
      (z.2.toNNReal : ℝ) - (τ z.1 : ℝ))
      ((P.prod (expMeasure p))[|{z : Ω × ℝ | τ z.1 < z.2.toNNReal}]) =
    Measure.map (fun t : ℝ => (t.toNNReal : ℝ))
      (expMeasure p) := by
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  let discount : ℝ≥0 → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (Real.exp (-(p * (a : ℝ))))
  have hTail (a : ℝ≥0) :
      (expMeasure p) {η : ℝ | a < η.toNNReal} = discount a :=
    avram_ws01e_b_exp_clock_toNNReal_strict_tail p hp a
  have hDiscount : Measurable discount := by
    fun_prop
  have hShift : ∀ a t : ℝ≥0,
      discount (a + t) = discount t * discount a := by
    intro a t
    exact avram_ws01e_b_exponential_nnreal_survival_memorylessness
      p hp a t
  have hZero : discount 0 = 1 := by
    simp [discount]
  have he : Measurable (fun t : ℝ => t.toNNReal) := by
    fun_prop
  exact avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
    P (expMeasure p) τ hτ Y hY hInd
      (fun t : ℝ => t.toNNReal) he discount hDiscount hTail
      discount hShift hZero hPos
