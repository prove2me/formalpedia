-- Prove2me | solution 1 for BookProof.InverseTransform.seedSet_measure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:12:55.232074+00:00
-- url     : https://prove2.me/submissions/2ae5c518-64b9-4a3e-9722-cbee6303b68d

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.seedSet_measure
import Mathlib
import Definitions.Def_ChapterInverseTransform
import Theorems.Thm_BookProof_InverseTransform_cdf_succ_sub
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    volume (seedSet p k) = ENNReal.ofReal (p k) := by

  rw [← cdf_succ_sub p k, seedSet, Real.volume_Ico]
