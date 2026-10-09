-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:30.194298+00:00
-- url     : https://prove2.me/submissions/060213b0-f57c-4cfc-87f2-e98ab37f50ca

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_kronecker
import Mathlib
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    BookProof.ChapterA3l.swap * (A ⊗ₖ B) = (B ⊗ₖ A) * BookProof.ChapterA3l.swap := by

  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp only [BookProof.ChapterA3l.swap, mul_apply, of_apply, kroneckerMap_apply, ite_mul,
      one_mul, zero_mul, mul_ite, mul_one, mul_zero];
  rw [ ← Finset.sum_filter ] ; rw [ ← Finset.sum_filter ] ;
  rw [ show ( Finset.univ.filter fun a : Fin 4 × Fin 4 => i = a.2 ∧ j = a.1 ) = { ( j, i ) } from
      ?_, show ( Finset.univ.filter fun a : Fin 4 × Fin 4 => a.1 = l ∧ a.2 = k ) = { ( l, k ) } from
          ?_ ] <;> norm_num;
  · ring;
  · grind;
  · grind
