-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_negative_generator_exact_ruin_landing_small_mark_truncation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:03:01.454735+00:00
-- url     : https://prove2.me/submissions/b15cc5f9-6966-4c19-861a-c6bd6b03b0d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At an exact zero landing the source small-jump correction is
present precisely when the prepayment reserve y lies strictly below 1.
At y = 1 the mark -1 is excluded by the original open truncation. -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 < y) :
    SpectrallyNegativeLevy.generatorIntegrand w y (-y) =
      if y < 1 then w 0 - w y + y * deriv w y
      else w 0 - w y := by
  unfold SpectrallyNegativeLevy.generatorIntegrand
  have hadd : y + -y = 0 := by ring
  rw [hadd]
  by_cases h : y < 1
  · have hmem : (-y : ℝ) ∈ Ioo (-1) 1 := by
      simp only [Set.mem_Ioo]
      constructor <;> linarith
    simp [Set.indicator, hmem, h] <;> ring
  · have hnot : (-y : ℝ) ∉ Ioo (-1) 1 := by
      intro hz
      exact h (by have hlow := hz.1; linarith)
    simp [Set.indicator, hnot, h]
