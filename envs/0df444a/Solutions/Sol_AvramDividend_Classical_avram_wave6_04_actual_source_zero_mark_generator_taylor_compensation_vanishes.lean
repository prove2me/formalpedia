-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_source_zero_mark_generator_taylor_compensation_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:19:10.484636+00:00
-- url     : https://prove2.me/submissions/c1434fd2-2653-4d8e-a49d-e908f36b256c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine source nonlinear jump generator vanishes at a zero
mark, justifying exclusion of zero jumps from the intrinsic X.X jump
count without altering the nonlinear Taylor drift. -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand w y 0 = 0 := by
  unfold SpectrallyNegativeLevy.generatorIntegrand
  simp
