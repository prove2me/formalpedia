-- Prove2me | solution 1 for BookProof.YangMillsHermite.gaussInt_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T01:53:48.223455+00:00
-- url     : https://prove2.me/submissions/1fa06aea-4741-426a-84c3-dfdca8df5e03

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.gaussInt_sub
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by

  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring
