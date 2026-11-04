-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_cutoff_band_compensation_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:11:06.576131+00:00
-- url     : https://prove2.me/submissions/c923ceaf-64ef-4d15-b433-45ea664f2012

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution (w : ℝ → ℝ) (y z ε : ℝ)
    (hε : 0 < ε) (hz : z ∈ Ioo (-1 : ℝ) (-ε)) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      w (y + z) - w y - deriv w y * z := by
  have hz0 : z < 0 := lt_trans hz.2 (neg_lt_zero.mpr hε)
  have hmem : z ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hz.1, lt_trans hz0 (by norm_num)⟩
  simp [SpectrallyNegativeLevy.generatorIntegrand,
    Set.indicator_of_mem hmem]
