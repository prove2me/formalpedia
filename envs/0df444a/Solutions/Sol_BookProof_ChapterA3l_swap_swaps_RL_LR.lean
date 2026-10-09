-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_swaps_RL_LR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:03:41.478315+00:00
-- url     : https://prove2.me/submissions/0ccd36e1-8d89-4daa-9cb4-925730c0fc5d

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_swaps_RL_LR
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * projRL = projLR * BookProof.ChapterA3l.swap := by

  unfold projLR projRL
  rw [swap_kronecker]
