-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.eval_gradPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:09:39.839983+00:00
-- url     : https://prove2.me/submissions/57a0ed56-3e44-41dc-a379-1c15152d893c

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.eval_gradPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_eval_linForm
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gradPoly v k) = ((gradFun v k x : ℝ) : ℂ) := by

  rw [gradPoly, gradFun, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, eval_linForm,
    Complex.ofReal_mul]
