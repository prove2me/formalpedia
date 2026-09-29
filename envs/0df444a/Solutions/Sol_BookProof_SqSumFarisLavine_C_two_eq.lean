-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.C_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:21.416045+00:00
-- url     : https://prove2.me/submissions/01ea7cce-3b07-4464-8b38-520cc19de337

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.C_two_eq
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
theorem solution : (C (2 : ℂ) : MvPolynomial (Fin D) ℂ) = 2 := by

  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, MvPolynomial.C_eq_coe_nat]
  norm_num
