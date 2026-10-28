-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_real_residual_clock_upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:56:03.084729+00:00
-- url     : https://prove2.me/submissions/7affa72f-b6f2-415c-8311-106f51d4bb51

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail

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
    (t : ℝ≥0) :
    (P.prod Q)[{z : Ω × Θ |
      (t : ℝ) < (e z.2 : ℝ) - (τ z.1 : ℝ)} |
      {z : Ω × Θ | τ z.1 < e z.2}] = factor t := by
  have h := (AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail P Q τ hτ Y hY hInd e he discount hd
    hTail factor hShift hPos t Set.univ MeasurableSet.univ).1
  have hset : {z : Ω × Θ | (t : ℝ) < (e z.2 : ℝ) - (τ z.1 : ℝ)} =
      {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ Set.univ} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    rw [← NNReal.coe_lt_coe, NNReal.coe_add]
    constructor <;> intro h <;> linarith
  rw [hset, h, Set.preimage_univ, measure_univ, mul_one]
