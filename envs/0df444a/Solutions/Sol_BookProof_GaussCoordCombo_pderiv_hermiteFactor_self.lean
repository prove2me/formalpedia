-- Prove2me | solution 1 for BookProof.GaussCoordCombo.pderiv_hermiteFactor_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:42:16.972473+00:00
-- url     : https://prove2.me/submissions/c4510b47-3537-444a-ab48-723e026bf663

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.pderiv_hermiteFactor_self
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_pderiv_aeval_self
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i (n + 1)) = ((n : ℂ) + 1) • hermiteFactor i n := by

  have hder : Polynomial.derivative (hermiteCx (n + 1)) = Polynomial.C ((n : ℂ) + 1) *
      hermiteCx n := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ n)
    simpa [hermiteCx, Polynomial.derivative_map] using h
  rw [hermiteFactor, pderiv_aeval_self, hder]
  simp [hermiteFactor, smul_eq_C_mul]
