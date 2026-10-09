-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:01:31.308634+00:00
-- url     : https://prove2.me/submissions/b864c235-f428-4aed-87a8-4140152797f3

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_sq
import Mathlib
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : BookProof.ChapterA3l.swap * BookProof.ChapterA3l.swap = 1 := by

  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [BookProof.ChapterA3l.swap, mul_apply, of_apply, mul_ite, mul_one, mul_zero];
  rw [ Finset.sum_eq_single ( l, k ) ] <;> aesop
