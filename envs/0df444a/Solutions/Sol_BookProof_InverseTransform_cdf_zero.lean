-- Prove2me | solution 1 for BookProof.InverseTransform.cdf_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:11:28.849662+00:00
-- url     : https://prove2.me/submissions/6e3f4c08-76af-4291-9f4a-52352672cb46

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.cdf_zero
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution : cdf p 0 = 0 := by

  simp [cdf]
