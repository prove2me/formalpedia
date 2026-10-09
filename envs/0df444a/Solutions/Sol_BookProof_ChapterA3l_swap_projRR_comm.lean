-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_projRR_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:03:06.80264+00:00
-- url     : https://prove2.me/submissions/7be8e8a5-ab17-4375-ace3-146aa3645ddb

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_projRR_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * projRR = projRR * BookProof.ChapterA3l.swap := by

  unfold projRR
  rw [swap_kronecker]
