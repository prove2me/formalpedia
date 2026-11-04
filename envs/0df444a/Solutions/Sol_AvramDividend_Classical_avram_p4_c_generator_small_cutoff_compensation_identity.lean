-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_small_cutoff_compensation_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:09.113654+00:00
-- url     : https://prove2.me/submissions/6da4a113-0b57-4989-84ef-2afed9a4365a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (w : ℝ → ℝ) (y z ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hz : z ∈ Ico (-ε) (0 : ℝ)) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      w (y + z) - w y - deriv w y * z := by
  have hmem : z ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · linarith [hz.1]
    · linarith [hz.2]
  simp [SpectrallyNegativeLevy.generatorIntegrand, Set.indicator_of_mem hmem]
