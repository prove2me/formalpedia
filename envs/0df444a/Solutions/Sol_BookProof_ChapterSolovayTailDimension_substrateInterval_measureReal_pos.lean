-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.substrateInterval_measureReal_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T12:25:04.722704+00:00
-- url     : https://prove2.me/submissions/df83f4bb-7cac-46f2-b992-2408093ede2c

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.substrateInterval_measureReal_pos
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateInterval_measure
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    0 < unitMeasure.real (substrateInterval n) := by

  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlt : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt hn1; linarith
  rw [measureReal_def, substrateInterval_measure, ENNReal.toReal_ofReal (by linarith)]
  linarith
