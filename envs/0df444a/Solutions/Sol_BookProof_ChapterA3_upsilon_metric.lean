-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_metric
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:36:28.146433+00:00
-- url     : https://prove2.me/submissions/c32e3136-1b96-498e-bf7f-1a1ccdfb5f54

import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3 Matrix
open scoped ComplexConjugate
set_option maxHeartbeats 0

private lemma metric_scaled (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (Upsilon T)ᵀ * minkowskiMat * Upsilon T =
      Complex.normSq T.det • minkowskiMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Upsilon, UpsilonC, pauliCoeff, pauliσ, minkowskiMat,
      minkowskiR, minkowskiZ, Matrix.mul_apply, Matrix.trace,
      Matrix.det_fin_two, Fin.sum_univ_four, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> simp <;> ring

theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    (Upsilon T)ᵀ * minkowskiMat * Upsilon T = minkowskiMat := by
  rw [metric_scaled, hT]
  simp

#print axioms solution
