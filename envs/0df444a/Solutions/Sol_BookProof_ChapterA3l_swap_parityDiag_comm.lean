-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:02:20.472978+00:00
-- url     : https://prove2.me/submissions/9986fdb1-43a4-4ff0-b596-575898c3141c

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * parityDiag = parityDiag * BookProof.ChapterA3l.swap := by

  unfold parityDiag
  rw [swap_kronecker]
