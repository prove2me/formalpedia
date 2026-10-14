-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.norm_bigP_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:08:40.356705+00:00
-- url     : https://prove2.me/submissions/9e6a7744-2ca1-4d26-a5f4-018f45085fbc

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.norm_bigP_sq
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_pgLp_sq
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_realCoeff_bigP
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_gaussInt_bigP
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
    ‖pgLp (bigP vf Mf)‖ ^ 2 = (∏ j, facS vf Mf j) * (Real.sqrt (2 * Real.pi)) ^ d := norm_pgLp_sq (realCoeff_bigP vf Mf) (gaussInt_bigP vf Mf)
