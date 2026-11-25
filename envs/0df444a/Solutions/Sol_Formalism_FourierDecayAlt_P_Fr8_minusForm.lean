-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.minusForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:44.273297+00:00
-- url     : https://prove2.me/submissions/86eec929-eb95-4c17-bead-0a816120416f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mon1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mon2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_comm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_io_comm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_i_b966c50babe5
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_b_8bb7912692ae
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_m_bi_189708a67289
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_GG
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_wt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_wt_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_c_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ct2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_gaussFormMinus
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution : MinusForm := by
  intro A S _ _ _ _ _ _ r L f b Yb hyp
  have G := gaussFormMinus A S r L f b Yb hyp
  obtain ⟨hS, h, hF, hr, h0, -, h1, -⟩ := hyp
  obtain ⟨-, -, -, -, fx, fxi, fc, -, -⟩ := hF
  show f.RR * ins b (f.TT Yb)ᵀ =
    star (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F) *
      (wt L ^ (f.N + 1) * (f.c * ins b !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb])) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  rw [G]
  have hEG : (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; 0, io L.ζi * io L.GG] * !![1, 0; f.m L Yb, 1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]
  have fE : FreeOf2 b (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_mul (free_io b _) (free_io b _))
  have fEH : FreeOf2 b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_mul (free_io b _) (free_io b _))
  have fW : FreeOf2 b (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_io b _)
  have hEH : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A))ᴴ =
      !![io L.ζi, 0; 0, io L.GG * io L.ζbi] := by
    rw [ct2, star_zero, star_mul, io_star, io_star, io_star, star_ζbi hS, star_ζi hS, star_GG hS]
  have hW : ins b (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) = wt L := by
    have e : (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) = d0 (wt L) := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [d0]
    rw [e, Wd1.insert_diagonal_extract]

  have dg : ∀ g ∈ zfns L, Commute (wt L ^ (f.N + 1) * f.c) (io g) := fun g hg =>
    ((wt_fn L hg).pow_left _).mul_left (h.c_fn g hg)
  have cE : Commute (wt L ^ (f.N + 1) * f.c) (ins b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A))) := by
    refine Wd1.ins_comm b _ _ (free_mul (free_pow (free_io b _) _) fc) ?_
    intro i j
    fin_cases i <;> fin_cases j
    · exact dg _ (mζi L)
    · exact Commute.zero_right _
    · exact Commute.zero_right _
    · exact (dg _ (mGG L)).mul_right (dg _ (mζbi L))

  have iz : (io L.ζ : SlopeTestRemainingChoices S A) * io L.ζi = 1 := by rw [← io_mul, L.ζ_ζi, io_one]
  have iw : (io L.ζb : SlopeTestRemainingChoices S A) * io L.ζbi = 1 := by rw [← io_mul, L.ζb_ζbi, io_one]
  have ig : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG, io_one]
  obtain ⟨x1, x2⟩ := h.x_xi _ h1
  have e00 : wt L * io L.ζi * (f.q (Yb - 1) • f.xi (Yb - 1)) * io L.ζbi =
      f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc, (comm_inv x1 x2 (h.x_fn _ _ (mζbi L))).eq, ← mul_assoc,
      wt_eq, mon1 iz iw (io_comm (fcomm L (mGGi L) (mζi L))) (io_comm (fcomm L (mζb L) (mζi L)))
        (io_comm (fcomm L (mGGi L) (mζbi L)))]
  have e11 : wt L * (io L.GG * io L.ζbi) * f.x Yb * (io L.ζi * io L.GG) = io L.GG * f.x Yb := by
    rw [mul_assoc, ((h.x_fn Yb _ (mζi L)).mul_right (h.x_fn Yb _ (mGG L))).eq, ← mul_assoc, wt_eq,
      mon2 iz iw ig]
  have key : f.d L * ins b !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb] =
      star (ins b !![io L.ζbi, 0; 0, io L.ζi * io L.GG]) *
        (wt L ^ (f.N + 1) * (f.c * ins b !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb])) *
        ins b !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Wd1.ins_star b _ fE, hEH, ← e00, ← e11, ← diag_mul, ← diag_mul, ← diag_mul]
    have f1 : FreeOf2 b (!![wt L, 0; 0, wt L] * !![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) := by
      rw [diag_mul]
      exact free2 (free_mul (free_io b _) (free_io b _)) (free_zero b) (free_zero b)
        (free_mul (free_io b _) (free_mul (free_io b _) (free_io b _)))
    have f2 : FreeOf2 b (!![wt L, 0; 0, wt L] * !![io L.ζi, 0; 0, io L.GG * io L.ζbi] *
        !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) := by
      rw [diag_mul, diag_mul]
      exact free2 (free_mul (free_mul (free_io b _) (free_io b _)) (free_smul _ (fxi _))) (free_zero b)
        (free_zero b) (free_mul (free_mul (free_io b _) (free_mul (free_io b _) (free_io b _))) (fx _))
    rw [Wd1.ins_mul b _ _ f2, Wd1.ins_mul b _ _ f1, Wd1.ins_mul b _ _ fW, hW]
    unfold FrameData.d
    generalize ins b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) = EH at cE ⊢
    generalize ins b (!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) = C
    generalize ins b (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) = E
    calc wt L ^ f.N * f.c * (wt L * EH * C * E) = wt L ^ f.N * (f.c * wt L) * EH * C * E := by
          simp only [mul_assoc]
      _ = (wt L ^ f.N * wt L * f.c) * EH * C * E := by rw [(c_wt h).eq]; simp only [mul_assoc]
      _ = (wt L ^ (f.N + 1) * f.c) * EH * C * E := by rw [pow_succ]
      _ = EH * (wt L ^ (f.N + 1) * f.c) * C * E := by rw [cE.eq]
      _ = EH * (wt L ^ (f.N + 1) * (f.c * C)) * E := by simp only [mul_assoc]
  rw [hEG, Wd1.ins_mul b _ _ fE, key]
  simp only [star_mul, mul_assoc]
end Formalism.FourierDecayAlt.P.Fr8
