-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:59:34.399978+00:00
-- url     : https://prove2.me/submissions/e60a28bb-552b-4ff5-b01a-fc1d2a0f5d50

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.displacedThermal_mean
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) (nbar : ℝ≥0) :
    ∫ x, x ∂(displacedThermal a nbar) = a := by

  simp [displacedThermal]
