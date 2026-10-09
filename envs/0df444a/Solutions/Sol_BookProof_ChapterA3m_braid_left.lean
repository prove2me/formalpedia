-- Prove2me | solution 1 for BookProof.ChapterA3m.braid_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:51.631978+00:00
-- url     : https://prove2.me/submissions/b13b82de-e646-4819-a15e-666659abca8c

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.braid_left
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
theorem solution : swap12 * swap23 * swap12 = swap13 := by

  ext a b; simp only [mul_apply] ;
  unfold swap12 swap23 swap13;
  simp only [kroneckerMap, ChapterA3l.swap, of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero];
  simp only [one_apply, Finset.sum_ite, not_and, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      mul_zero];
  split_ifs <;> simp_all only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      not_and];
  · rw [ Finset.sum_eq_single ( ( a.1.2, a.2 ), a.1.1 ) ]
    · simp only [Nat.cast_eq_one]
      rw [ Finset.card_eq_one ] ; use ( ( a.1.2, a.1.1 ), a.2 ) ; ext ; aesop
    · simp [ * ]
      aesop
    · simp [ * ]
  · rw [ Finset.sum_eq_zero ] ; aesop
