-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.re_inner_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:20.538457+00:00
-- url     : https://prove2.me/submissions/2fe2ed40-89f8-457b-b901-563468f14e54

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.re_inner_symm
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a b : L2d D) :
    (inner ℂ a b : ℂ).re = (inner ℂ b a : ℂ).re := by

  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_re]
