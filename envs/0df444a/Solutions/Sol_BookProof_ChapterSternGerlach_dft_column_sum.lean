-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.dft_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:41.428343+00:00
-- url     : https://prove2.me/submissions/9ede1ac1-7429-4fbd-8476-123ac67901f9

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.dft_column_sum
import Mathlib
import Definitions.Def_ChapterSternGerlach
import Theorems.Thm_BookProof_ChapterSternGerlach_dft_normSq
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ∑ i, Complex.normSq (dftMatrix n i j) = 1 := by

  rw [Finset.sum_congr rfl (fun i _ => dft_normSq n hn i j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
