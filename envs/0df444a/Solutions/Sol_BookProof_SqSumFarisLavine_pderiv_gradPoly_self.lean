-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.pderiv_gradPoly_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:09:41.217981+00:00
-- url     : https://prove2.me/submissions/d21214ea-505e-4e0d-b11d-6bcc2818ba4a

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.pderiv_gradPoly_self
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_linForm
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (gradPoly v k) = C (((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ)) := by

  rw [gradPoly, map_sum, Complex.ofReal_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_linForm, ← map_mul]
  congr 1
  push_cast
  ring
