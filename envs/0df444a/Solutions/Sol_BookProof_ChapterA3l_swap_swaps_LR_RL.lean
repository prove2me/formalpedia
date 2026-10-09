-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_swaps_LR_RL
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:03:18.91391+00:00
-- url     : https://prove2.me/submissions/e416b5d7-22ec-4d8c-8b42-1ab76c649366

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_swaps_LR_RL
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * projLR = projRL * BookProof.ChapterA3l.swap := by

  unfold projLR projRL
  rw [swap_kronecker]
