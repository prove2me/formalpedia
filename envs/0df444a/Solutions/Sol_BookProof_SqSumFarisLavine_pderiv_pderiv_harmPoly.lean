-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:21.646412+00:00
-- url     : https://prove2.me/submissions/258d8254-692f-4eee-99a1-56e644d5b6fc

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_harmPoly
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin D) :
    pderiv j (pderiv j (harmPoly (d := D))) = C (1 / 2 : ℂ) := by

  rw [pderiv_harmPoly, pderiv_C_mul, pderiv_X_self, mul_one]
