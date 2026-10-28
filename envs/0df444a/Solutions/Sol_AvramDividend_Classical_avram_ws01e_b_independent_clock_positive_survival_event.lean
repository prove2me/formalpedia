-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_independent_clock_positive_survival_event
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:01:26.344188+00:00
-- url     : https://prove2.me/submissions/9887da16-8506-43a6-99e4-5526450758c4

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hTailPos : ∀ a : ℝ≥0, 0 < Q {η : Θ | a < e η}) :
    (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0 := by
  have hS : MeasurableSet {z : Ω × Θ | τ z.1 < e z.2} :=
    measurableSet_lt (hτ.comp measurable_fst) (he.comp measurable_snd)
  rw [Measure.prod_apply hS]
  have hpos : ∀ x : Ω, 0 < Q (Prod.mk x ⁻¹' {z : Ω × Θ | τ z.1 < e z.2}) := fun x => hTailPos (τ x)
  have hmeas : Measurable (fun x : Ω => Q (Prod.mk x ⁻¹' {z : Ω × Θ | τ z.1 < e z.2})) :=
    measurable_measure_prodMk_left hS
  intro h0
  rw [lintegral_eq_zero_iff hmeas] at h0
  have : ∀ᵐ x ∂P, False := by
    filter_upwards [h0] with x hx
    exact (hpos x).ne' hx
  rw [ae_iff] at this
  simp at this
