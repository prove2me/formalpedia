-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:35:07.9737+00:00
-- url     : https://prove2.me/submissions/b423d8cd-9110-498c-9756-cdf9d02cc0d7

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_rectangle_factor

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
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    IndepFun
      (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      (fun z : Ω × Θ => Y z.1)
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  exact AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_rectangle_factor
    P Q τ hτ Y hY hInd e he discount hd hTail factor hShift hPos A hA B hB
