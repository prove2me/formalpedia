-- Prove2me | solution 1 for BookProof.ChapterA3m.swap12_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:56.440023+00:00
-- url     : https://prove2.me/submissions/a9fc2489-f8ea-4692-b529-52531fc608b6

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap12_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap12_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : swap12 * parityDiag3 = parityDiag3 * swap12 := by

  exact swap12_kronecker _ _ _
