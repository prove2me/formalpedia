-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_restrict_identities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:06:44.532497+00:00
-- url     : https://prove2.me/submissions/b1461515-8d43-43e0-829c-cc0373384eaa

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Both restrictions leave the source compact negative-mark measure fixed. -/
theorem solution :
    (((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))).restrict
      (Iio (0 : ℝ)) =
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ∧
    (((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))).restrict
      (Ioo (-1 : ℝ) 0) =
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by
  constructor
  · rw [Measure.restrict_restrict measurableSet_Iio]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨h.2, h⟩
  · rw [Measure.restrict_restrict measurableSet_Ioo]
    simp only [inter_self]