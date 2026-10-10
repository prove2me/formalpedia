-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.dgamma_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:20:00.917044+00:00
-- url     : https://prove2.me/submissions/2bfc7fd7-1ae3-490f-a90e-5fce931d158f

import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open Matrix


theorem solution (μ : Fin 4) :
    (dgamma μ)ᴴ = if μ = 0 then dgamma μ else -dgamma μ := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dgamma, mgamma, mgammaZ, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.of_apply, cons_val_zero, cons_val_succ, cons_val_one, cons_val_two,
      RingHom.mapMatrix_apply, Int.cast_neg, Int.cast_ofNat, Int.cast_one, one_apply,
      star_zero, star_neg, Complex.conj_I, map_zero, map_neg]
