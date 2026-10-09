-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_chir2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:33.404427+00:00
-- url     : https://prove2.me/submissions/64d13418-1958-4744-90e3-d5cda7b48bcf

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_chir2
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * chir2 = chir1 * BookProof.ChapterA3l.swap := by

  unfold chir1 chir2
  rw [swap_kronecker]
