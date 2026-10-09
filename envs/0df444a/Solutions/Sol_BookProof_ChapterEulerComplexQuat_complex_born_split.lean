-- Prove2me | solution 1 for BookProof.ChapterEulerComplexQuat.complex_born_split
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:41:47.777976+00:00
-- url     : https://prove2.me/submissions/7ff943bd-9e1d-4714-816a-8e3d87b2701f

-- Generated from ChapterEulerComplexQuat.lean — solution of BookProof.ChapterEulerComplexQuat.complex_born_split
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat



open scoped Quaternion BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (k : Fin n) :
    cbornProb v k = (v k).re ^ 2 + (v k).im ^ 2 := by

  simp [cbornProb, Complex.normSq_apply]; ring
