-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_indicator_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:06:38.746248+00:00
-- url     : https://prove2.me/submissions/b8abd5e2-cbed-4a05-a5fa-33fd9ecad246

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The small-jump indicator is one on the measure's entire support. -/
theorem solution :
    ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)),
      (Ioo (-1 : ℝ) 0).indicator (1 : ℝ → ℝ) y = 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  simp [Set.indicator_of_mem hy]