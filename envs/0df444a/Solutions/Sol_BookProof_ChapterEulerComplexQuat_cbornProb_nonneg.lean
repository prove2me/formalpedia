-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.cbornProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:42:00.564755+00:00
-- url     : https://prove2.me/submissions/12d0054e-ae3b-4a65-b65a-4af2106cb16c

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.cbornProb_nonneg
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (k : Fin n) : 0 ≤ cbornProb v k := Complex.normSq_nonneg _
