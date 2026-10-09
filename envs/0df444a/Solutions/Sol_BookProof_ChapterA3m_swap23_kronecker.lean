-- Prove2me | solution 1 for BookProof.ChapterA3m.swap23_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:40:37.29331+00:00
-- url     : https://prove2.me/submissions/1a98bf36-2b6f-4858-b029-b5a06c56b53e

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap23_kronecker
import Mathlib
import Definitions.Def_ChapterA3m
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    swap23 * ((A ⊗ₖ B) ⊗ₖ C) = ((A ⊗ₖ C) ⊗ₖ B) * swap23 := by

  ext a col;
  simp only [swap23, mul_apply, of_apply, kroneckerMap_apply, ite_mul, one_mul, zero_mul, mul_ite,
      mul_one, mul_zero];
  rw [ Finset.sum_eq_single ( ( a.1.1, a.2 ), a.1.2 ), Finset.sum_eq_single ( ( col.1.1, col.2 ),
      col.1.2 ) ] <;> simp +contextual [ eq_comm ];
  · ring;
  · aesop
