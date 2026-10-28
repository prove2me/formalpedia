-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrateInterval_measure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:03.600001+00:00
-- url     : https://prove2.me/submissions/3ff0f9a3-dcea-401a-af24-3e7a40370cfa

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrateInterval_measure
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateInterval_subset
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    unitMeasure (substrateInterval n)
      = ENNReal.ofReal (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by

  have hrestr : unitMeasure = volume.restrict (Icc (0 : ℝ) 1) := rfl
  rw [hrestr, Measure.restrict_apply (substrateInterval_measurableSet n),
    Set.inter_eq_left.mpr (substrateInterval_subset n), substrateInterval, Real.volume_Ioc]
