-- Prove2me | solution 1 for AvramDividend.Classical.ripple_between_stopping_times_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:05:10.308049+00:00
-- url     : https://prove2.me/submissions/ac953e51-a011-4771-8cc3-1c5080ff9344

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
open MeasureTheory Set
open scoped NNReal

/-- The genuinely random stochastic window (sigma,tau] is predictable.
Adapted from Ripple/Stochastic/ContinuousItoStoppedIsometry.lean,
stopping_indicator_sub, commit e216e28ce3ffb43877e11f71be260e40a37a35df
(Apache-2.0); both windows need to be stopping times. -/
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) (σ τ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable]
      {z : ℝ≥0 × Ω |
        0 < z.1 ∧ σ z.2 < (z.1 : WithTop ℝ≥0) ∧
          (z.1 : WithTop ℝ≥0) ≤ τ z.2} := by
  have heq :
      {z : ℝ≥0 × Ω |
        0 < z.1 ∧ σ z.2 < (z.1 : WithTop ℝ≥0) ∧
          (z.1 : WithTop ℝ≥0) ≤ τ z.2} =
      {z : ℝ≥0 × Ω |
        0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2} \
        {z : ℝ≥0 × Ω |
          0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ σ z.2} := by
    ext z
    simp only [mem_setOf_eq, mem_diff]
    constructor
    · rintro ⟨hpos, hσlt, hτle⟩
      exact ⟨⟨hpos, hτle⟩, fun hs => (not_le.mpr hσlt) hs.2⟩
    · rintro ⟨⟨hpos, hτle⟩, hn⟩
      exact ⟨hpos, lt_of_not_ge (fun hz => hn ⟨hpos, hz⟩), hτle⟩
  rw [heq]
  exact (AvramDividend.Classical.ripple_stopping_region_predictable F τ hτ).diff
    (AvramDividend.Classical.ripple_stopping_region_predictable F σ hσ)
