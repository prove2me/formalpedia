-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.coreD_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:47.986141+00:00
-- url     : https://prove2.me/submissions/6fa2cde7-9c2c-4964-a0ca-7ea0f0ecfb30

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.coreD_neg
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
theorem solution (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (-p) = -coreD j p := by

  rw [show (-p) = (-1 : ℂ) • p by rw [neg_smul, one_smul], coreD_smul, neg_smul, one_smul]
