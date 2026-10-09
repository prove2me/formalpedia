-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.commForm_eq_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:43:21.425439+00:00
-- url     : https://prove2.me/submissions/1335de55-556a-4fb4-b8c9-f927d8c66918

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.commForm_eq_im
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_sqSumOp_pgLp
import Theorems.Thm_BookProof_SqSumFarisLavine_harmCore_symmetricOn
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_sub
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
import Theorems.Thm_BookProof_QgHermiteOscillator_harmCore_pgLp
import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_symmetricOn
open BookProof.SqSumFarisLavine




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commForm (sqSumOp kappa v) harmCore ⟨pgLp p, pgLp_mem_core p⟩
      = -(gaussInt (cpoly p * commPoly kappa v p)).im := by

  have hHu : sqSumOp kappa v ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (BookProof.SqSumFarisLavine.sqSumPoly kappa v p) :=
    sqSumOp_pgLp kappa v p
  have hNu : harmCore (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := D)) = pgLp (harmP p) :=
    harmCore_pgLp p
  have h1 : (inner ℂ (sqSumOp kappa v ⟨pgLp p, pgLp_mem_core p⟩)
        (harmCore (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := D))) : ℂ)
      = gaussInt (cpoly p * BookProof.SqSumFarisLavine.sqSumPoly kappa v (harmP p)) := by
    have hs := sqSumOp_symmetricOn kappa v ⟨pgLp p, pgLp_mem_core p⟩
      ⟨pgLp (harmP p), pgLp_mem_core (harmP p)⟩
    rw [hNu, hs, sqSumOp_pgLp, inner_pgLp_pgLp]
  have h2 : (inner ℂ (harmCore (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := D)))
        (sqSumOp kappa v ⟨pgLp p, pgLp_mem_core p⟩) : ℂ)
      = gaussInt (cpoly p * harmP (BookProof.SqSumFarisLavine.sqSumPoly kappa v p)) := by
    have hs := harmCore_symmetricOn (D := D) ⟨pgLp p, pgLp_mem_core p⟩
      ⟨pgLp (BookProof.SqSumFarisLavine.sqSumPoly kappa v p), pgLp_mem_core (BookProof.SqSumFarisLavine.sqSumPoly kappa v p)⟩
    rw [hHu, hs, harmCore_pgLp, inner_pgLp_pgLp]
    simp only [BookProof.GaussCoreQuadBounds.harmP,
      BookProof.GaussCoreQuadBounds.harmPoly,
      BookProof.QgHermiteOscillator.harmPoly]
  have hz : gaussInt (cpoly p * commPoly kappa v p)
      = gaussInt (cpoly p * BookProof.SqSumFarisLavine.sqSumPoly kappa v (harmP p))
        - gaussInt (cpoly p * harmP (BookProof.SqSumFarisLavine.sqSumPoly kappa v p)) := by
    rw [commPoly, mul_sub, gaussInt_sub]
  rw [commForm, h1, h2, ← hz]
  simp [Complex.mul_re]
