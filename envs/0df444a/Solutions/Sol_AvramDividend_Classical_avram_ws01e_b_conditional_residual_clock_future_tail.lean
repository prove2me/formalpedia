-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:09:58.654141+00:00
-- url     : https://prove2.me/submissions/5d9bd809-7ff6-421f-9a50-2ea1b91822f3

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_residual_clock_survival_shift
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_clock_tail_future_event_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0)
    (t : ℝ≥0) (B : Set β) (hB : MeasurableSet B) :
    ((P.prod Q)[{z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      factor t * P (Y ⁻¹' B)) ∧
    ((P.prod Q)[{z : Ω × Θ | Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      P (Y ⁻¹' B)) := by
  have hmt : MeasurableSet {z : Ω × Θ | τ z.1 < e z.2} :=
    measurableSet_lt (hτ.comp measurable_fst) (he.comp measurable_snd)
  have hfin : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ ⊤ := measure_ne_top _ _
  have hcancel : ∀ x : ℝ≥0∞, ((P.prod Q) {z : Ω × Θ | τ z.1 < e z.2})⁻¹ *
      ((P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} * x) = x := by
    intro x
    rw [← mul_assoc, ENNReal.inv_mul_cancel hPos hfin, one_mul]
  constructor
  · rw [cond_apply hmt]
    have h1 : {z : Ω × Θ | τ z.1 < e z.2} ∩ {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} =
        {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp]
      intro h
      exact lt_of_le_of_lt (le_self_add) h.1
    rw [h1, AvramDividend.Classical.avram_ws01e_b_residual_clock_survival_shift P Q τ hτ Y hY hInd
      e he discount hd hTail factor hShift t B hB]
    rw [mul_comm (factor t), mul_assoc, hcancel]
  · rw [cond_apply hmt]
    have h1 : {z : Ω × Θ | τ z.1 < e z.2} ∩ {z : Ω × Θ | Y z.1 ∈ B} =
        {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} := rfl
    rw [h1, AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor P Q τ hτ Y hY
      hInd e he discount hd hTail B hB, hcancel]
