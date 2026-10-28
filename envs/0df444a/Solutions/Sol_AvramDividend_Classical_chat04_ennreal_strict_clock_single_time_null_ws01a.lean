-- Prove2me | solution 1 for AvramDividend.Classical.chat04_ennreal_strict_clock_single_time_null_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:10:54.806983+00:00
-- url     : https://prove2.me/submissions/88f14547-ca75-4feb-bb52-7afdf324a1fc

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The equality instant of an extended stopping clock is negligible in time. -/
theorem solution (τ : ℝ≥0∞) :
    (volume : Measure ℝ) {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} = 0 := by
  have hsubset :
      {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} ⊆ {τ.toReal} := by
    rintro t ⟨ht, heq⟩
    change t = τ.toReal
    rw [← heq]
    exact (ENNReal.toReal_ofReal ht).symm
  exact Measure.mono_null hsubset (measure_singleton τ.toReal)
