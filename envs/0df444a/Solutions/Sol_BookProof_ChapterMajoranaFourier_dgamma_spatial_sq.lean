-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.dgamma_spatial_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:30.758024+00:00
-- url     : https://prove2.me/submissions/630fc82b-6ba2-4164-93cf-50516972c0f5

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix


theorem solution (i : Fin 3) : dgamma i.succ * dgamma i.succ = -1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [dgamma, mgamma, mgammaZ, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_four,
      Matrix.of_apply, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two,
      RingHom.mapMatrix_apply, Int.cast_neg, Int.cast_ofNat, Int.cast_one, one_apply,
      Complex.I_sq, neg_mul, mul_neg, neg_neg]
