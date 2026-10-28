-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_rectangle_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:23:20.216525+00:00
-- url     : https://prove2.me/submissions/ba092e25-3228-42b4-8bcd-8bb4ffa1a632

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_clock_kernel_future_event_factor
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
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ |
        ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ |
          ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ A} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        (P.prod Q)[{z : Ω × Θ | Y z.1 ∈ B} |
          {z : Ω × Θ | τ z.1 < e z.2}] := by
  have hK : MeasurableSet {z : ℝ≥0 × Θ | ((e z.2 : ℝ) - (z.1 : ℝ)) ∈ A} := by
    have : Measurable (fun z : ℝ≥0 × Θ => (e z.2 : ℝ) - (z.1 : ℝ)) := by fun_prop
    exact this hA
  rw [AvramDividend.Classical.avram_ws01e_b_conditional_clock_kernel_future_event_factor
    P Q τ hτ Y hY hInd e he (fun a η => ((e η : ℝ) - (a : ℝ)) ∈ A) hK B hB]
  rw [(AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail
    P Q τ hτ Y hY hInd e he discount hd hTail factor hShift hPos 0 B hB).2]
