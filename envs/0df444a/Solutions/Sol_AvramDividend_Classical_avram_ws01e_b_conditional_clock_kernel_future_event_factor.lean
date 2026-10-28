-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_conditional_clock_kernel_future_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:10:41.126319+00:00
-- url     : https://prove2.me/submissions/ffc3f170-5115-4680-ac0d-e77833e1bda1

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_arbitrary_clock_kernel_future_event_factor

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
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q)[{z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      (P.prod Q)[{z : Ω × Θ | K (τ z.1) z.2} |
          {z : Ω × Θ | τ z.1 < e z.2}] *
        P (Y ⁻¹' B) := by
  let K' : ℝ≥0 → Θ → Prop := fun a η => a < e η ∧ K a η
  have hK' : MeasurableSet {z : ℝ≥0 × Θ | K' z.1 z.2} := by
    refine MeasurableSet.inter ?_ hK
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hfac := AvramDividend.Classical.avram_ws01e_b_arbitrary_clock_kernel_future_event_factor
    P Q τ hτ Y hY hInd K' hK' (fun a => Q (Prod.mk a ⁻¹' {z : ℝ≥0 × Θ | K' z.1 z.2}))
    (measurable_measure_prodMk_left hK') (fun a => rfl) B hB
  have hmt : MeasurableSet {z : Ω × Θ | τ z.1 < e z.2} :=
    measurableSet_lt (hτ.comp measurable_fst) (he.comp measurable_snd)
  rw [cond_apply hmt, cond_apply hmt]
  have h1 : {z : Ω × Θ | τ z.1 < e z.2} ∩ {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} =
      {z : Ω × Θ | K' (τ z.1) z.2 ∧ Y z.1 ∈ B} := by
    ext z; simp [K', and_assoc]
  have h2 : {z : Ω × Θ | τ z.1 < e z.2} ∩ {z : Ω × Θ | K (τ z.1) z.2} =
      {z : Ω × Θ | K' (τ z.1) z.2} := by
    ext z; simp [K']
  rw [h1, h2, hfac, mul_assoc]
