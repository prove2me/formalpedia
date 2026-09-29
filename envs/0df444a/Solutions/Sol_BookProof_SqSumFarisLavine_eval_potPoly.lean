-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.eval_potPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:09:40.527903+00:00
-- url     : https://prove2.me/submissions/0c371483-fc09-41be-9c54-0dcebfdddc3c

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.eval_potPoly
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
theorem solution (v : R → Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (potPoly v) = ((potFun v x : ℝ) : ℂ) := by

  rw [potPoly, potFun, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_sum,
    Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, eval_linForm, ← Complex.ofReal_mul, ← pow_two]
