-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_projLL_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:02:54.575762+00:00
-- url     : https://prove2.me/submissions/b4277370-c395-4552-b8db-6ee0f2e34bf6

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_projLL_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * projLL = projLL * BookProof.ChapterA3l.swap := by

  unfold projLL
  rw [swap_kronecker]
