-- Prove2me | solution 1 for BookProof.ChapterA3l.projSym_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:03:53.2596+00:00
-- url     : https://prove2.me/submissions/7e3867d8-ad97-4677-b2d8-459be7779e48

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projSym_idem
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_sq
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : projSym * projSym = projSym := by

  unfold projSym
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have key : (1 + BookProof.ChapterA3l.swap) * (1 + BookProof.ChapterA3l.swap) = (2 : ℂ) • (1 + BookProof.ChapterA3l.swap) := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, swap_sq]
    module
  rw [key, smul_smul]
  norm_num
