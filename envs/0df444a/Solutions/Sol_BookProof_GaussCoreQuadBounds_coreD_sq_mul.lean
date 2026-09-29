-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.coreD_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T14:00:00.474251+00:00
-- url     : https://prove2.me/submissions/d257050b-33bb-4511-96a2-98f6414f2a25

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs
open MvPolynomial

variable {D : ℕ}

theorem solution (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD j (f * p))
      = pderiv j (pderiv j f) * p + (2 : ℂ) • (pderiv j f * coreD j p)
        + f * coreD j (coreD j p) := by
  have hmul (a b : MvPolynomial (Fin D) ℂ) :
      coreD j (a * b) = pderiv j a * b + a * coreD j b := by
    unfold coreD
    simp [pderiv_mul]
    ring
  rw [hmul, coreD_add, hmul, hmul]
  set z := pderiv j f * coreD j p
  trans pderiv j (pderiv j f) * p + (z + z) + f * coreD j (coreD j p)
  · ring
  · simp [z, two_smul, nsmul_eq_mul, smul_eq_mul] <;> ring
