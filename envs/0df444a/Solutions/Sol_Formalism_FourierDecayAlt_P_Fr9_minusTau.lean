-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.minusTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:25:54.565821+00:00
-- url     : https://prove2.me/submissions/3faf1a92-3a6a-477c-bfc6-fe0f123446cd

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ins_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_rht_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_frameM
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_freeOf2_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_tau_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_tau_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_lhs_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_rhs_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hatN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_frame_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_diag_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution : MinusTau := by
  intro A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hf, hr, hb, hb1, hbm, hq⟩ Y hY
  obtain ⟨hY, hd⟩ := hY
  have hd : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr hd
  obtain ⟨H, -⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨hrtt, -, -, h3, h4, -⟩ := H
  have hF := hf.2.2.1
  have hk : (Yb - Y) • (f.m L Yb * f.hatT Y 1 1 - f.hatT Y 1 1 * f.m L Yb) =
      f.hatT Y 0 1 - f.hatT Y 1 1 * f.m L Yb := by
    refine tau_key (h3 Yb hb).2 (h4 Yb Y) ?_ (hrtt Yb Y 0 1 1 1)
    rw [frameM hS h hr hb hbm, hat_τ h (h.inv_reg hb)]
  have c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact (io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm
  have c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact ((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left
      ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)
  have hτfree : FreeOf b (f.hatT Y 1 1) := by
    rw [hat_τ h hY]; exact Wd11.free_mul (Wd11.free_io b _) (hf.2.2.2.2.1 Y)
  show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F *
      (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 1 =
    io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  have hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b)
      (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hf _))
      (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))
  have hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1]) :=
    fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b)
      (free_smul _ hτfree) i j)
  rw [frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 1), ← mul_assoc (io L.GG), ← hat_τ h hY,
    ins_left hτfree, diag_mat _ hd, rhs_red hW, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.smul_mul, tau_mat c1 c2 hk]
end Formalism.FourierDecayAlt.P.Fr9
