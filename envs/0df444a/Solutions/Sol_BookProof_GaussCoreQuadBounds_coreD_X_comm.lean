-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.coreD_X_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:37:20.433055+00:00
-- url     : https://prove2.me/submissions/98614c51-16bf-4a2a-b70e-8607ea228d83

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs
open MvPolynomial

variable {D : ℕ}

theorem solution (j : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (X j * p) - X j * coreD j p = p := by
  unfold coreD
  simp [pderiv_mul, pderiv_X_self]
  ring
