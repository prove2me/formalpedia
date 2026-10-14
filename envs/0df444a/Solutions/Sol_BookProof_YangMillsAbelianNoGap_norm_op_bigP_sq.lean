-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.norm_op_bigP_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:09:24.978068+00:00
-- url     : https://prove2.me/submissions/ac08c287-ca99-4c67-937a-2f536c9005f7

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.norm_op_bigP_sq
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_pgLp_sq
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_realCoeff_bigP
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_gaussInt_op_bigP
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
import Theorems.Thm_BookProof_YangMillsHermite_starP_pderiv
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterSqueezedGaussStates
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
theorem solution (c : Fin d) (α γ : ℝ) :
    ‖pgLp (((α : ℝ) : ℂ) • (X c * bigP vf Mf) + ((γ : ℝ) : ℂ) • pderiv c (bigP vf Mf))‖ ^ 2
      = (coordComboSum (opCoef α γ (vf c) (Mf c)) 1 (Mf c))
        * (∏ j ∈ Finset.univ.erase c, facS vf Mf j) * (Real.sqrt (2 * Real.pi)) ^ d := by

  refine norm_pgLp_sq ?_ (gaussInt_op_bigP vf Mf c α γ)
  refine RealCoeff.add (RealCoeff.smul ?_) (RealCoeff.smul ?_)
  · exact RealCoeff.mul (realCoeff_X c) (realCoeff_bigP vf Mf)
  · rw [RealCoeff, starP_pderiv, show starP (bigP vf Mf) = bigP vf Mf from realCoeff_bigP vf Mf]
