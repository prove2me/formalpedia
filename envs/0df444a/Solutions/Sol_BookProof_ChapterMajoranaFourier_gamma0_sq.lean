-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.gamma0_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:10:20.723038+00:00
-- url     : https://prove2.me/submissions/6694ec0f-1cfa-49e9-aa8d-217b4bd2338a

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix

theorem solution : dgamma 0 * dgamma 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dgamma, mgamma, mgammaZ, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four,
      Matrix.of_apply, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two,
      RingHom.mapMatrix_apply, Int.cast_neg, Int.cast_ofNat, Int.cast_one, one_apply,
      Complex.I_sq, neg_mul, mul_neg, neg_neg]
