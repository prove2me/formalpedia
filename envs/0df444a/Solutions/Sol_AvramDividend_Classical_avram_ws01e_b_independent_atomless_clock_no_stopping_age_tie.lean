-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:55:16.172003+00:00
-- url     : https://prove2.me/submissions/d3ff06ba-28ee-496d-bf13-a6cd8857f188

import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set
open scoped NNReal ENNReal

/-- An independent atomless observation clock has zero probability of a tie
with any measurable random stopping age, even when the age depends on the
whole underlying Lévy path. The proof is a genuine product-space Tonelli
argument, with no path stopping identity or Wiener–Hopf factor assumed. -/

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hAtomless : ∀ a : ℝ≥0, Q {η : Θ | e η = a} = 0) :
    (P.prod Q) {z : Ω × Θ | τ z.1 = e z.2} = 0 := by
  have hS : MeasurableSet {z : Ω × Θ | τ z.1 = e z.2} :=
    measurableSet_eq_fun (hτ.comp measurable_fst) (he.comp measurable_snd)
  rw [Measure.prod_apply hS]
  have : ∀ x : Ω, Q (Prod.mk x ⁻¹' {z : Ω × Θ | τ z.1 = e z.2}) = 0 := by
    intro x
    have h : Prod.mk x ⁻¹' {z : Ω × Θ | τ z.1 = e z.2} = {η : Θ | e η = τ x} := by
      ext η; simp [eq_comm]
    rw [h, hAtomless]
  simp only [this, MeasureTheory.lintegral_zero]
