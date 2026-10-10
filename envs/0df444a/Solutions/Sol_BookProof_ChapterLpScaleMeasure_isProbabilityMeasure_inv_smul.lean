-- Prove2me | solution 1 for BookProof.ChapterLpScaleMeasure.isProbabilityMeasure_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:27:10.172483+00:00
-- url     : https://prove2.me/submissions/7fb5eb02-c42c-47c1-8600-93c9495d2863

-- Generated from ChapterLpScaleMeasure.lean — solution of BookProof.ChapterLpScaleMeasure.isProbabilityMeasure_inv_smul
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure



noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure nu] (hne : nu Set.univ ≠ 0) :
    IsProbabilityMeasure ((nu Set.univ)⁻¹ • nu) := by

  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne (measure_ne_top nu _)
