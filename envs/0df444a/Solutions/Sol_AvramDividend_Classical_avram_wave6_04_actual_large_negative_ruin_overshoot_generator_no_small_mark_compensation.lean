-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_large_negative_ruin_overshoot_generator_no_small_mark_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:03:05.427609+00:00
-- url     : https://prove2.me/submissions/d302f44f-d11d-4e7f-8b34-0a4e54e736e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For a genuine source negative Lévy mark at most -1 that strictly
overshoots ruin, the original open (-1,1) truncation vanishes and the
negative extension makes the exact generator increment -w(y). -/
theorem solution
    (w : ℝ → ℝ) (y z : ℝ)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hy : 0 < y) (hz_large : z ≤ -1) (hover : y + z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand w y z = -w y := by
  have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
    intro hz
    exact (not_lt_of_ge hz_large) hz.1
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [hw_neg (y + z) hover]
  simp [Set.indicator, hnot]
