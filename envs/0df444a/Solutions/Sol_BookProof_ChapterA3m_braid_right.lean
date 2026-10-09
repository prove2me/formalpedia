-- Prove2me | solution 1 for BookProof.ChapterA3m.braid_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:52.615201+00:00
-- url     : https://prove2.me/submissions/4fd23c9d-c1b2-4bf3-b775-f46bc8b07ed7

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.braid_right
import Mathlib
import Definitions.Def_ChapterA3m
import Definitions.Def_ChapterA3l
open BookProof
open BookProof.ChapterA3l
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : swap23 * swap12 * swap23 = swap13 := by

  unfold swap12 swap23 swap13;
  ext a b; simp only [kroneckerMap, mul_apply, of_apply, ite_mul, one_mul, zero_mul, mul_ite,
      mul_one, mul_zero] ;
  simp only [ChapterA3l.swap, of_apply, one_apply, mul_ite, mul_one, mul_zero];
  rw [ Finset.sum_eq_single ( ( b.1.1, b.2 ), b.1.2 ) ] <;> simp only [and_self, ↓reduceIte,
      Finset.mem_univ, ne_eq, ite_eq_right_iff, and_imp, forall_const, Prod.forall, Prod.mk.injEq,
          not_and, not_true_eq_false, IsEmpty.forall_iff];
  · rw [ Finset.sum_eq_single ( ( b.2, b.1.1 ), b.1.2 ) ] <;> aesop;
  · aesop
