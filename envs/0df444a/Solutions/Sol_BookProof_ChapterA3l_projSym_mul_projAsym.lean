-- Prove2me | solution 1 for BookProof.ChapterA3l.projSym_mul_projAsym
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:04:06.747693+00:00
-- url     : https://prove2.me/submissions/7ed2faa6-dc71-458d-8c3e-84465b84d07f

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projSym_mul_projAsym
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_sq
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : projSym * projAsym = 0 := by

  unfold projSym projAsym
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have key : (1 + BookProof.ChapterA3l.swap) * (1 - BookProof.ChapterA3l.swap) = 0 := by
    rw [add_mul, one_mul, mul_sub, mul_one, swap_sq]
    abel
  rw [key, smul_zero]
