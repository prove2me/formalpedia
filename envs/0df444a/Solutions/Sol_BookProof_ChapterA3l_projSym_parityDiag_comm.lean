-- Prove2me | solution 1 for BookProof.ChapterA3l.projSym_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:39:15.967979+00:00
-- url     : https://prove2.me/submissions/e942a237-ff08-4d2b-91a8-23b7bdfec07c

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projSym_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_parityDiag_comm
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : projSym * parityDiag = parityDiag * projSym := by

  unfold projSym
  rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul, mul_one,
    swap_parityDiag_comm]
