-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.dgamma_spatial_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:33.13911+00:00
-- url     : https://prove2.me/submissions/2b001b15-8fdd-46f9-85b1-39a847cb1e07

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix


theorem solution (i j : Fin 3) (h : i ≠ j) :
    dgamma i.succ * dgamma j.succ = -(dgamma j.succ * dgamma i.succ) := by
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl h) <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [dgamma, mgamma, mgammaZ, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four,
      Matrix.of_apply, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two,
      RingHom.mapMatrix_apply, Int.cast_neg, Int.cast_ofNat, Int.cast_one, one_apply,
      Complex.I_sq, neg_mul, mul_neg, neg_neg]
