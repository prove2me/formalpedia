-- Prove2me | solution 1 for BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:09.590627+00:00
-- url     : https://prove2.me/submissions/e06ca0f0-5878-43eb-a37d-4d12a811f410

-- Generated from ChapterQuantumGravityHalfDensity.lean — solution of BookProof.QuantumGravityHalfDensity.qgSrcMeasure_eq_withDensity_halfDensity_sq
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Theorems.Thm_BookProof_QuantumGravityHalfDensity_qgSrcMeasure_density_eq_halfDensity_sq
open BookProof.QuantumGravityHalfDensity




open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution :
    qgSrcMeasure
      = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          fun y => ENNReal.ofReal (qgHalfDensity y ^ 2) := by

  rw [qgSrcMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [qgSrcMeasure_density_eq_halfDensity_sq (le_of_lt hy)]
