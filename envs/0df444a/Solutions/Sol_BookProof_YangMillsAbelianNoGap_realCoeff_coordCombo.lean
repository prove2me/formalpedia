-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.realCoeff_coordCombo
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:13.802273+00:00
-- url     : https://prove2.me/submissions/2f80ee4f-5b58-48f7-b6b2-ffe1d0e0d04b

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.realCoeff_coordCombo
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_realCoeff_hermiteFactor
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (c : ℕ → ℝ) (p K : ℕ) :
    RealCoeff (coordCombo i c p K) := by

  refine RealCoeff.sum fun k _ => ?_
  exact RealCoeff.smul (realCoeff_hermiteFactor i _)
