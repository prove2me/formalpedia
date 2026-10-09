-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.quat_born_split
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:42:29.180198+00:00
-- url     : https://prove2.me/submissions/fa346d80-6d38-452f-b80a-b4f3e72051ee

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.quat_born_split
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℍ[ℝ]) (k : Fin n) :
    qbornProb v k =
      (v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2 := by

  simp [qbornProb, Quaternion.normSq_def']
