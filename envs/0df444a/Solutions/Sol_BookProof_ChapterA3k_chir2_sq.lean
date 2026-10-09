-- Prove2me | solution 1 for BookProof.ChapterA3k.chir2_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:38:04.485254+00:00
-- url     : https://prove2.me/submissions/37e2b789-050b-4fee-83dc-3d2383a3c768

-- Generated from ChapterA3k.lean — solution of BookProof.ChapterA3k.chir2_sq
import Mathlib
import Definitions.Def_ChapterA3k
import Theorems.Thm_BookProof_ChapterA3j_chir_sq
open BookProof.ChapterA3k



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution : chir2 * chir2 = -1 := by

  unfold chir2;
  convert congr_arg ( fun x : Matrix ( Fin 4 ) ( Fin 4 ) ℂ => ( 1 : Matrix ( Fin 4 ) ( Fin 4 ) ℂ )
      ⊗ₖ x ) BookProof.ChapterA3j.chir_sq using 1;
  · ext i j; simp only [mul_apply, kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_zero] ;
    split_ifs <;> simp_all only [↓reduceIte, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        ite_self];
    refine Finset.sum_bij ( fun x hx => x.2 ) ?_ ?_ ?_ ?_ <;> aesop;
  · ext i j ; fin_cases i <;> fin_cases j <;> norm_num
