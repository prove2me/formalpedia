-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.tauNN_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:00:46.916417+00:00
-- url     : https://prove2.me/submissions/433a9eea-a01c-40a7-8257-76b6ea458ea1

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.tauNN_pos
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


@[simp] private theorem tauNN_coe (nbar : ℝ≥0) : ((tauNN nbar : ℝ≥0) : ℝ) = (nbar : ℝ) + 1 / 2 := by
  simp [tauNN]

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) : 0 < (tauNN nbar : ℝ) := by

  rw [tauNN_coe]; positivity
