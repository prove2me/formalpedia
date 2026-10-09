-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_creation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:21.686873+00:00
-- url     : https://prove2.me/submissions/9b12a2fd-7f17-4acf-9cd9-286af63ed822

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_creation
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_leibniz_prime
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_sub_prime
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt ((X i * p - pderiv i p) * q) = gaussInt (p * pderiv i q) := by

  have hleib := gaussInt_leibniz_prime i p q
  have h1 : (X i * p - pderiv i p) * q = X i * (p * q) - pderiv i p * q := by ring
  rw [h1, gaussInt_sub_prime]
  linear_combination -hleib
