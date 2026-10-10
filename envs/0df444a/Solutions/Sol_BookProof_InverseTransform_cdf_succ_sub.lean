-- Prove2me | solution 1 for BookProof.InverseTransform.cdf_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:12:11.325745+00:00
-- url     : https://prove2.me/submissions/3623aae4-9c69-4cc7-b9e4-2e2724b401a8

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.cdf_succ_sub
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : cdf p (k + 1) - cdf p k = p k := by

  unfold cdf
  rw [Finset.sum_range_succ]
  ring
