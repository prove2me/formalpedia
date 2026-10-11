-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.rotMat_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:33.834094+00:00
-- url     : https://prove2.me/submissions/161a4e77-96f9-43d8-bff9-d851cc07f0c0

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.rotMat_isUnit
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Theorems.Thm_BookProof_ProbabilityClockStochastic_rotMat_det
import Definitions.Def_ChapterFullQuadraticEsa
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) : IsUnit (rotMat a) := by

  rw [Matrix.isUnit_iff_isUnit_det, rotMat_det]; exact isUnit_one
