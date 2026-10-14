-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.gaussInt_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:16.098105+00:00
-- url     : https://prove2.me/submissions/6273d07e-e583-4c4e-af4c-f358a8e43097

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.gaussInt_one_eq
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    gaussInt (1 : MvPolynomial (Fin d) ℂ) = (((Real.sqrt (2 * Real.pi)) ^ d : ℝ) : ℂ) := by

  have h0 : (monomial (0 : Fin d →₀ ℕ) (1 : ℂ)) = 1 := by simp
  have h := gaussInt_monomial (0 : Fin d →₀ ℕ)
  rw [h0] at h
  have hm : gaussMoment 0 = Real.sqrt (2 * Real.pi) := by
    simpa [gaussMoment] using BookProof.HermiteCore.gint_one
  rw [h]
  simp [hm]
