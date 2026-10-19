-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:57:04.938287+00:00
-- url     : https://prove2.me/submissions/1c2cfaa7-bdba-4f2f-a342-e933b456e535

import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.displacedThermal_variance
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


theorem solution (a : ℝ) (nbar : ℝ≥0) :
    Var[id; displacedThermal a nbar] = (nbar : ℝ) + 1 / 2 := by
  rw [displacedThermal, ProbabilityTheory.variance_id_gaussianReal, tauNN]
  push_cast; ring

