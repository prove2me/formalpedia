-- Prove2me | solution 1 for BookProof.GaussCoordCombo.gaussInt_sub_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:20.588073+00:00
-- url     : https://prove2.me/submissions/8e968f0c-c4a6-490c-b878-b5fdfd6cdb08

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.gaussInt_sub'
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by

  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring
