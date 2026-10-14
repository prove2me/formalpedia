-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.realCoeff_bigP
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:08:11.522976+00:00
-- url     : https://prove2.me/submissions/0be02264-1968-4cce-aee8-90db779c262b

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.realCoeff_bigP
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_realCoeff_prod
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_realCoeff_facW
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution : RealCoeff (bigP vf Mf) := realCoeff_prod fun j _ => realCoeff_facW vf Mf j
