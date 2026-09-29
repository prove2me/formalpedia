-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.eval_linForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:50.434992+00:00
-- url     : https://prove2.me/submissions/a787f190-1054-408f-bcc5-352bfd5eaed8

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.eval_linForm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linForm v) = ((linFun v x : ℝ) : ℂ) := by

  rw [linForm, linFun, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Complex.ofReal_mul]
