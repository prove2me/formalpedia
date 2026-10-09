-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:03:12.802556+00:00
-- url     : https://prove2.me/submissions/041f1bc0-b210-4f30-ae1e-3717d4c3ec6e

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.inverseTemperature_pos
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) : 0 < inverseTemperature nbar := by

  rw [inverseTemperature]
  positivity
