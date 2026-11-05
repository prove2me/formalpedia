-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_weighted_exp_image_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:24:54.377481+00:00
-- url     : https://prove2.me/submissions/b7d0b718-6497-4851-8397-a39c1f17a49d

import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- An exponential pushforward has no atom at zero, regardless of
the source mass or nonnegative weight. -/
theorem solution (σ : Measure ℝ) (w : ℝ → ℝ≥0∞) :
    ((σ.withDensity w).map Real.exp) ({0} : Set ℝ) = 0 := by
  have hs : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
  rw [Measure.map_apply Real.measurable_exp hs]
  have hpre : Real.exp ⁻¹' ({0} : Set ℝ) = ∅ := by
    ext x
    simp [Real.exp_ne_zero]
  simp [hpre]
