-- Prove2me | solution 1 for BookProof.ChapterA3l.projAsym_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:39:39.639267+00:00
-- url     : https://prove2.me/submissions/8b64ef4c-121d-43ff-a18c-ef6a2c1ae105

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projAsym_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_parityDiag_comm
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution :
    projAsym * parityDiag = parityDiag * projAsym := by

  unfold projAsym
  rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, one_mul, mul_one,
    swap_parityDiag_comm]
