-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.core_eq_pgLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:49.149119+00:00
-- url     : https://prove2.me/submissions/ee60c133-ef51-4dfd-90a5-75545a36be61

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.core_eq_pgLp
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
theorem solution (u : polyGaussCore (d := D)) :
    ∃ p : MvPolynomial (Fin D) ℂ, u = ⟨pgLp p, pgLp_mem_core p⟩ := by

  obtain ⟨p, hp⟩ := u.2
  exact ⟨p, Subtype.ext hp.symm⟩
