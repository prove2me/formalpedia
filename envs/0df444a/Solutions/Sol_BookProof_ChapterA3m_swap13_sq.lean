-- Prove2me | solution 1 for BookProof.ChapterA3m.swap13_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:41:29.299407+00:00
-- url     : https://prove2.me/submissions/344ee6d7-3736-438f-ac1e-9f6c7f83d078

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap13_sq
import Mathlib
import Definitions.Def_ChapterA3m
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : swap13 * swap13 = 1 := by

  ext a b; simp only [swap13] ;
  simp only [mul_apply, of_apply, mul_ite, mul_one, mul_zero, one_apply];
  rw [ Finset.sum_eq_single ( ( b.2, b.1.2 ), b.1.1 ) ] <;> aesop
