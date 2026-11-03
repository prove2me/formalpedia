-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_source_generator_negative_unit_mark_is_uncompensated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:03:10.922218+00:00
-- url     : https://prove2.me/submissions/405312c4-17d0-4e5b-ad4b-5672cefcf713

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The unit negative Lévy mark is outside the original *open*
small-mark compensation interval (-1,1), and its full nonlinear jump
is treated as a large negative jump. -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand w y (-1) =
      w (y - 1) - w y := by
  unfold SpectrallyNegativeLevy.generatorIntegrand
  have hnot : (-1 : ℝ) ∉ Ioo (-1 : ℝ) 1 := by simp
  simp [Set.indicator, hnot, sub_eq_add_neg]
