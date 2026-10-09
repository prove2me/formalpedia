-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_chir1
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:32.388992+00:00
-- url     : https://prove2.me/submissions/87405de7-52fd-4e76-94a0-0362c653964c

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_chir1
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * chir1 = chir2 * BookProof.ChapterA3l.swap := by

  unfold chir1 chir2
  rw [swap_kronecker]
