-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.minusL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:09.881595+00:00
-- url     : https://prove2.me/submissions/a97d59de-23de-45d8-8a73-007162636672

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ins_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_rht_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_comm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_freeOf2_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_d0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mk2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_lhs_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_rhs_red
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hatN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_frame_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_diag_mat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_eeConj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_add_matrix2_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ins_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_l_mat
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_h_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps
import Theorems.Thm_Formalism_YangianSpanCharacter_P_minus_frame_identity


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
theorem _root_.solution : MinusL := by
  intro A S _ _ _ _ _ _ r L f b Yb ⟨hS, h, hfr, hr, hb, hb1, hbm, hq⟩ Y hY hY1
  obtain ⟨hYi, hd0, hd1⟩ := hY
  obtain ⟨hY1i, -, -⟩ := hY1
  have hY := h.inv_reg hYi
  have hd : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hne : Y ≠ Yb := fun e => hd0 (by rw [e, sub_self])
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have MF := Formalism.YangianSpanCharacter.P.minus_frame_identity ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Y Yb hYi hY1i hb hb1 hbm hd0 hd
  obtain ⟨-, -, m3, m4, m5⟩ := MF
  rw [Hl Y hYi hY1i] at m3 m5
  rw [hat_m hS h hr hb hbm] at m4 m5
  have hF := hfr.2.2.1
  have hxi := hfr.2.2.2.2.2.1
  have c1 : Commute (io L.ζbi : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact (io_comm (zc L (mζbi L) (mG L))).mul_right (h.x_fn Y _ (mζbi L)).symm
  have c2 : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (f.hatT Y 1 1) := by
    rw [hat_τ h hY]
    exact ((io_comm (zc L (mζi L) (mG L))).mul_right (h.x_fn Y _ (mζi L)).symm).mul_left
      ((Commute.refl _).mul_right (h.x_fn Y _ (mG L)).symm)
  have hτfree : FreeOf b (f.hatT Y 1 1) := by
    rw [hat_τ h hY]; exact Wd11.free_mul (Wd11.free_io b _) (hfr.2.2.2.2.1 Y)
  have hQ : f.hatQ (Yb - 1) = f.q (Yb - 1) := by
    simp [FrameData.hatQ, h.inv_reg hbm, h.inv_reg hb]
  have xif : ∀ u ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi u) (io g) := fun u hu g hg =>
    comm_inv (h.x_xi u hu).1 (h.x_xi u hu).2 (h.x_fn u g hg)
  have xixi : Commute (f.xi (Yb - 1)) (f.xi Yb) :=
    comm_inv (h.x_xi _ hbm).1 (h.x_xi _ hbm).2
      (comm_inv (h.x_xi _ hb).1 (h.x_xi _ hb).2 (h.x_commute Yb (Yb - 1))).symm
  show ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F *
      (Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 0 =
    io L.GG * (f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]) *
      (io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0;
        -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))),
        f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L]) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  have hP : FreeOf2 b (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_matrix_entries (Wd11.free_io b _) (Wd11.free_zero b)
      (Wd11.free_mul (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _)) (free_m hfr _))
      (Wd11.free_mul (Wd11.free_io b _) (Wd11.free_io b _))
  have hW : FreeOf2 b ((Yb - Y - 1)⁻¹ • !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1]) :=
    fun i j => free_smul _ (freeOf2_matrix_entries (free_smul _ hτfree) (Wd11.free_zero b) (Wd11.free_zero b)
      (free_smul _ hτfree) i j)
  have hk : FreeOf b (kapL L : SlopeTestRemainingChoices S A) := Wd11.free_io b _
  have hlm : FreeOf2 b !![f.l L Y, 0;
      -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] :=
    freeOf2_matrix_entries (free_l hfr _) (Wd11.free_zero b)
      (free_neg (Wd11.free_mul hk (free_smul _ (Wd11.free_mul (hxi _) (hxi _)))))
      (free_add (free_l hfr _) (Wd11.free_mul hk (Wd11.free_io b _)))
  have lins : io (L.l0 Y) + kapL L * ins b !![f.ee Y, 0;
        -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))),
        f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L] =
      ins b !![f.l L Y, 0;
        -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] := by
    rw [eeConj h hYi hY1i hb hb1 hne, ins_left hk, ← Wd1.insert_diagonal_extract b (io (L.l0 Y)), ← ins_add, d0_eq, d0_eq,
      Matrix.mul_fin_two, add_matrix2_of]
    congr 1
    unfold FrameData.l
    refine mk2 ?_ ?_ ?_ ?_
    · rw [zero_mul, add_zero]
    · simp
    · rw [zero_mul, zero_add, zero_add, mul_neg]
    · rw [zero_mul, zero_add, mul_add, add_assoc]
  have pf : (!![io L.ζbi, 0; io L.ζi * io L.GG * f.m L Yb, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; 0, io L.ζi * io L.GG] * !![1, 0; f.m L Yb, 1] := by
    rw [Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_ <;> simp
  have e1 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) *
        !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] =
      !![(Yb - Y) • f.hatT Y 1 1, 0; 0, (Yb - Y - 1) • f.hatT Y 1 1] *
        !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_
    · simp only [mul_zero, add_zero]
      rw [mul_smul_comm, smul_mul_assoc, c1.eq]
    · simp
    · simp
    · simp only [mul_zero, zero_add]
      rw [mul_smul_comm, smul_mul_assoc, c2.eq]
  have e2 : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) *
        !![f.l L Y, 0; -((Yb - Y - 1)⁻¹ • Formalism.YangianSpanCharacter.Y.hf (fun Y => io L.GGi * f.xi Y) f.hatQ (Yb - 1)), f.l L Y] =
      !![f.l L Y, 0;
        -(kapL L * ((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1)))), f.l L Y + kapL L * tz L] *
        !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine mk2 ?_ ?_ ?_ ?_
    · simp only [zero_mul, mul_zero, add_zero]
      rw [ζbi_l h]
    · simp
    · unfold Formalism.YangianSpanCharacter.Y.hf
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [hQ, sub_add_cancel]
      exact h_entry (xif _ hbm) (xif _ hb) xixi _ _
    · simp only [mul_zero, zero_add]
      rw [ζiGG_l h]
  rw [lins, frame_mat, rht_row, lhs_red hF hP (hatN h hY _ _ 0), ← mul_assoc (io L.GG), ← hat_τ h hY,
    ins_left hτfree, diag_mat _ hd, ← Wd1.ins_mul _ _ _ hW, rhs_red (Wd11.freeOf2_mul hW hlm), Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, pf, l_mat m3 m4 m5 e1 e2]
end Formalism.FourierDecayAlt.P.Fr9
