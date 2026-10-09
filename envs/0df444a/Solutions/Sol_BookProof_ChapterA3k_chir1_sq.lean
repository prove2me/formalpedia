-- Prove2me | solution 1 for BookProof.ChapterA3k.chir1_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:37:52.229983+00:00
-- url     : https://prove2.me/submissions/40c151d8-8f24-4620-922e-9f9e85f936f4

-- Generated from ChapterA3k.lean — solution of BookProof.ChapterA3k.chir1_sq
import Mathlib
import Definitions.Def_ChapterA3k
import Theorems.Thm_BookProof_ChapterA3j_chir_sq
open BookProof.ChapterA3k



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution : chir1 * chir1 = -1 := by

  -- Unfold the definition of `chir1` as `chir ⊗ₖ 1`.
  unfold chir1;
  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp only [mul_apply, kroneckerMap_apply, neg_apply] ; ring;
  convert congr_arg ( fun m : Matrix ( Fin 4 ) ( Fin 4 ) ℂ => m i k * ( if j = l then 1 else 0 ) ) (
      BookProof.ChapterA3j.chir_sq ) using 1 <;> simp only [one_apply, mul_ite, mul_one, mul_zero,
          ite_mul, zero_mul, mul_apply, Prod.mk.injEq, neg_apply] ; focus (ring);
  · erw [ Finset.sum_product ] ; aesop;
  · rw [show (-1 : M2) (i, j) (k, l) = -(if (i, j) = (k, l) then 1 else 0) from rfl,
        show (-1 : Matrix (Fin 4) (Fin 4) ℂ) i k = -(if i = k then 1 else 0) from rfl]
    simp only [Prod.mk.injEq]
    grind
