-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.gaussInt_bigP
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:08:39.274984+00:00
-- url     : https://prove2.me/submissions/e0e71c3d-25a1-4114-847d-0d040c3555e1

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.gaussInt_bigP
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_gaussInt_one_eq
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_coordFactor_facW
import Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_prod_coordFactor
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution :
    gaussInt (bigP vf Mf * bigP vf Mf)
      = (((∏ j, facS vf Mf j) * (Real.sqrt (2 * Real.pi)) ^ d : ℝ) : ℂ) := by

  have h := gaussInt_prod_coordFactor (S := (Finset.univ : Finset (Fin d)))
    (W := facW vf Mf) (s := facS vf Mf) (fun j _ => coordFactor_facW vf Mf j)
    (R := 1) (fun j _ => by simp)
  rw [mul_one] at h
  rw [bigP, h, gaussInt_one_eq]
  push_cast
  ring
