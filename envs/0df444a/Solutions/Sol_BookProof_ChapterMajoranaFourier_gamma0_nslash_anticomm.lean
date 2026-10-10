-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.gamma0_nslash_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:26:19.035397+00:00
-- url     : https://prove2.me/submissions/0e6b8e90-394b-429e-9d53-955239da66ae

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix

theorem solution (n : Fin 3 → ℝ) :
    dgamma 0 * nslash n = -(nslash n * dgamma 0) := by
  have hn : nslash n =
      (n 0 : ℂ) • dgamma 1 + ((n 1 : ℂ) • dgamma 2 + (n 2 : ℂ) • dgamma 3) := by
    simp [nslash, Fin.sum_univ_three, add_assoc]
  rw [hn]
  simp only [mul_add, add_mul, mul_smul, smul_mul_assoc, smul_neg]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [dgamma, mgamma, mgammaZ, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four,
      Matrix.of_apply, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two,
      RingHom.mapMatrix_apply, Int.cast_neg, Int.cast_ofNat, Int.cast_one, one_apply,
      Complex.I_sq, neg_mul, mul_neg, neg_neg, add_assoc]
