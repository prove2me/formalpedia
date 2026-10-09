-- Prove2me | solution 1 for BookProof.ChapterA3m.swap13_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:47:10.691845+00:00
-- url     : https://prove2.me/submissions/72b6bf25-4da1-40a8-aef1-491c8af1b122

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap13_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap13_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : swap13 * parityDiag3 = parityDiag3 * swap13 := by

  have := @swap13_kronecker;
  exact this _ _ _
