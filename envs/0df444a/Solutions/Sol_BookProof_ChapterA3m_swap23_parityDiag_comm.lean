-- Prove2me | solution 1 for BookProof.ChapterA3m.swap23_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:47:09.559762+00:00
-- url     : https://prove2.me/submissions/79762935-9ce8-474e-816e-eaf8883f3ab0

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap23_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap23_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : swap23 * parityDiag3 = parityDiag3 * swap23 := by

  exact swap23_kronecker _ _ _
