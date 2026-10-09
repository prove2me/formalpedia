-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_leibniz_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:06.930753+00:00
-- url     : https://prove2.me/submissions/93912c78-e13e-4c0e-8b0a-15fe563afd20

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_leibniz'
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv i P * Q) + gaussInt (P * pderiv i Q) = gaussInt (X i * (P * Q)) := by

  rw [← gaussInt_pderiv i (P * Q), ← gaussInt_add]
  congr 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring
