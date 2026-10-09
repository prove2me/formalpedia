-- Prove2me | solution 1 for BookProof.ChapterA3l.projAsym_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:39:27.644797+00:00
-- url     : https://prove2.me/submissions/8cc7d628-0aa7-4385-a470-7e0562a21bcf

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projAsym_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_spinGenDiag_comm
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    projAsym * spinGenDiag μ ν = spinGenDiag μ ν * projAsym := by

  unfold projAsym
  rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, one_mul, mul_one,
    swap_spinGenDiag_comm]
