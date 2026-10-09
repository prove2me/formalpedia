-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:03:49.62049+00:00
-- url     : https://prove2.me/submissions/93b7373f-4727-4df5-9539-8760f8ff0782

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_zero
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution : inverseTemperature 0 = 1 / 2 := by

  rw [inverseTemperature]
  norm_num
