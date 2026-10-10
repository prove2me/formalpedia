-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:00:45.434986+00:00
-- url     : https://prove2.me/submissions/10ed8b21-0c4f-4095-bb59-c3f603c2a135

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.tauNN_eq_thermalTemperature
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open BookProof.ChapterCoherentTemperature


@[simp] private theorem tauNN_coe (nbar : ℝ≥0) : ((tauNN nbar : ℝ≥0) : ℝ) = (nbar : ℝ) + 1 / 2 := by
  simp [tauNN]

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) :
    ((tauNN nbar : ℝ≥0) : ℝ)
      = BookProof.ChapterCoherentTemperature.thermalTemperature (nbar : ℝ) := by

  rw [tauNN_coe, BookProof.ChapterCoherentTemperature.thermalTemperature]
