-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.norm_op_bigP_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:09:25.948496+00:00
-- url     : https://prove2.me/submissions/117df277-879d-4fe1-8b83-03c74e1aa7ee

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.norm_op_bigP_le
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_gaussConst_pos
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_facS_pos
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_bigP_sq
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_op_bigP_sq
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin d) (α γ ε : ℝ)
    (h : coordComboSum (opCoef α γ (vf c) (Mf c)) 1 (Mf c) ≤ ε * facS vf Mf c) :
    ‖pgLp (((α : ℝ) : ℂ) • (X c * bigP vf Mf) + ((γ : ℝ) : ℂ) • pderiv c (bigP vf Mf))‖ ^ 2
      ≤ ε * ‖pgLp (bigP vf Mf)‖ ^ 2 := by

  classical
  have hprod : (∏ j, facS vf Mf j)
      = facS vf Mf c * ∏ j ∈ Finset.univ.erase c, facS vf Mf j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ c)).symm
  have hrest : 0 ≤ ∏ j ∈ Finset.univ.erase c, facS vf Mf j :=
    Finset.prod_nonneg fun j _ => (facS_pos vf Mf j).le
  have hG : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi)) ^ d := (gaussConst_pos (d := d)).le
  rw [norm_op_bigP_sq, norm_bigP_sq, hprod]
  have hfactor : 0 ≤ (∏ j ∈ Finset.univ.erase c, facS vf Mf j)
      * (Real.sqrt (2 * Real.pi)) ^ d := mul_nonneg hrest hG
  nlinarith [h, hfactor]
