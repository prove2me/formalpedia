-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.dtOverlap_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:01:35.254818+00:00
-- url     : https://prove2.me/submissions/9110da64-85c4-4317-907f-19cfd54f4d6c

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.dtOverlap_pos
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_eq
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) (a b : ℝ) : 0 < dtOverlap nbar a b := by

  rw [dtOverlap_eq]
  have : (0 : ℝ) < (nbar : ℝ) + 1 / 2 := by positivity
  positivity
