-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.qbornProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:42:30.136096+00:00
-- url     : https://prove2.me/submissions/5532b423-5770-4186-adba-2b0a97a39440

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.qbornProb_nonneg
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
import Theorems.Thm_BookProof_ChapterEulerComplexQuat_quat_born_split
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℍ[ℝ]) (k : Fin n) : 0 ≤ qbornProb v k := by

  rw [quat_born_split]; positivity
