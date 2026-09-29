-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.pderiv_harmPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:09:27.842302+00:00
-- url     : https://prove2.me/submissions/139ec50d-5b17-4239-9702-0fd9bd504dc7

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.pderiv_harmPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_C_two_eq
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin D) :
    pderiv j (harmPoly (d := D)) = C (1 / 2 : ℂ) * X j := by

  rw [harmPoly, map_sum, Finset.sum_eq_single j]
  · rw [show (X j : MvPolynomial (Fin D) ℂ) ^ 2 = X j * X j by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X_self, one_mul, mul_one,
      show (X j + X j : MvPolynomial (Fin D) ℂ) = C (2 : ℂ) * X j by rw [C_two_eq]; ring,
      ← mul_assoc, ← map_mul]
    norm_num
  · intro i _ hi
    rw [show (X i : MvPolynomial (Fin D) ℂ) ^ 2 = X i * X i by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X]
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h
