-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.coreD_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:21:51.326846+00:00
-- url     : https://prove2.me/submissions/a292cf87-441f-48b6-a6a8-a95593892da5

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs

noncomputable section
variable {D : ℕ}

theorem solution (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (f * p) = pderiv j f * p + f * coreD j p := by
  simp [coreD, pderiv_mul]
  ring
