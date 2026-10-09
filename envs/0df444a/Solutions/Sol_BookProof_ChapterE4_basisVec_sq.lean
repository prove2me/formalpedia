-- Prove2me | solution 1 for BookProof.ChapterE4.basisVec_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:49.561806+00:00
-- url     : https://prove2.me/submissions/42056238-5ece-41ba-8c61-c7fc2a0777d9

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.basisVec_sq
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (k i : ℕ) : (basisVec k i) ^ 2 = if i = k then 1 else 0 := by

  unfold basisVec; aesop;
