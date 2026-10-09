-- Prove2me | solution 1 for BookProof.ChapterA3m.swap12_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:40:14.540068+00:00
-- url     : https://prove2.me/submissions/2d81c797-b41d-4d10-8c99-2fe1a3e15055

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap12_kronecker
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    swap12 * ((A ⊗ₖ B) ⊗ₖ C) = ((B ⊗ₖ A) ⊗ₖ C) * swap12 := by

  -- By definition of swap12, we have swap12 = swap ⊗ₖ 1.
  have h_swap12 : swap12 = BookProof.ChapterA3l.swap ⊗ₖ 1 := by
    exact?;
  rw [ h_swap12, ← Matrix.mul_kronecker_mul ];
  rw [ ← Matrix.mul_kronecker_mul ];
  rw [ BookProof.ChapterA3l.swap_kronecker ] ; norm_num
