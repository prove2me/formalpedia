-- Prove2me | solution 1 for AvramDividend.Classical.ripple_stopping_region_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:58:19.911131+00:00
-- url     : https://prove2.me/submissions/490ce8da-09f3-4e5a-bec5-a05270e09f8c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_after_stop_eq_iUnion

open MeasureTheory Set
open scoped NNReal

/-- Predictability of the stopped stochastic interval.
Adapted from zinan-huang/Ripple, StoppedPredictableIntegrand.lean
(commit e216e28ce3ffb43877e11f71be260e40a37a35df; Apache-2.0). -/
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable]
      {z : ℝ≥0 × Ω | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2} := by
  have hafterMeas :
      MeasurableSet[F.predictable]
        {z : ℝ≥0 × Ω | τ z.2 < (z.1 : WithTop ℝ≥0)} := by
    rw [AvramDividend.Classical.ripple_after_stop_eq_iUnion τ]
    exact MeasurableSet.iUnion fun q =>
      measurableSet_predictable_Ioi_prod
        (hτ.measurableSet_le (Real.toNNReal (q : ℝ)))
  have heq :
      {z : ℝ≥0 × Ω | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2} =
        (Ioi (0 : ℝ≥0) ×ˢ (univ : Set Ω)) \
          {z | τ z.2 < (z.1 : WithTop ℝ≥0)} := by
    ext z
    simp only [mem_setOf_eq, mem_diff, mem_prod, mem_Ioi, mem_univ, and_true]
    constructor
    · rintro ⟨hpos, hle⟩
      exact ⟨hpos, not_lt.mpr hle⟩
    · rintro ⟨hpos, hnot⟩
      exact ⟨hpos, not_lt.mp hnot⟩
  rw [heq]
  exact (measurableSet_predictable_Ioi_prod (𝓕 := F) (i := 0)
    MeasurableSet.univ).diff hafterMeas
