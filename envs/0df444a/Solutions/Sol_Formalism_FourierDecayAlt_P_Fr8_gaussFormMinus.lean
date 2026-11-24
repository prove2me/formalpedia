-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.gaussFormMinus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:30.370807+00:00
-- url     : https://prove2.me/submissions/648eacb6-12b0-49e8-9228-c576c83e2bb9

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_free2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ins2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ins_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_di_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_d_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_ct2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_asm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps
import Theorems.Thm_Formalism_FourierDecayAlt_P_gauss_decomp_minus_letter


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
theorem _root_.solution : GaussFormMinus := by
  intro A S _ _ _ _ _ _ r L f b Yb hyp
  obtain ⟨hS, h, hF, hr, h0, -, h1, -⟩ := hyp
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨-, -, -, fFi, fx, fxi, fc, fci, fee⟩ := hF
  have h1' : Yb - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hdm := d_m hS h Yb hr h0 h1
  have hm : mf f.hatT (fun Y => io L.GGi * f.xi Y) Yb = f.m L Yb := by
    unfold FrameData.m
    rw [mul_assoc, ← hdm, ← mul_assoc, di_d h, one_mul]
  have G := gauss_decomp_minus_letter ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Yb h0 h1
  have hQ : f.hatQ (Yb - 1) = f.q (Yb - 1) := by
    simp [FrameData.hatQ, h.inv_reg h1, h.inv_reg h0]
  have hτ : f.hatT Yb 1 1 = io L.GG * f.x Yb := by
    have : f.hatT Yb 1 1 = f.F * f.TT Yb 1 1 * f.Fi := by simp [FrameData.hatT, h.inv_reg h0]
    rw [this, h.frame_τ Yb (h.inv_reg h0), mul_assoc, h.F_Fi, mul_one]
  rw [hm, Hl (Yb - 1) h1 h1', hQ, hτ] at G
  rw [hm] at hdm
  have hT : (f.TT Yb)ᵀ = (f.hatT Yb)ᵀ.map (fun c => f.Fi * c * f.F) := by
    refine Matrix.ext fun i j => ?_
    have : f.hatT Yb j i = f.F * f.TT Yb j i * f.Fi := by simp [FrameData.hatT, h.inv_reg h0]
    rw [Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply, this]
    calc f.TT Yb j i = (f.Fi * f.F) * f.TT Yb j i * (f.Fi * f.F) := by rw [h.Fi_F, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]

  have fd : FreeOf b (f.d L) := free_mul (free_pow (free_io b _) _) fc
  have fdi : FreeOf b (f.di L) := free_mul fci (free_pow (free_io b _) _)
  have fl : FreeOf b (f.l L (Yb - 1)) := free_add (free_io b _) (free_mul (free_io b _) (fee _))
  have fm : FreeOf b (f.m L Yb) := free_mul (free_mul fdi (free_star fl)) fd
  have fU : FreeOf2 b !![1, f.l L (Yb - 1); 0, 1] := free2 (free_one b) fl (free_zero b) (free_one b)
  have fD : FreeOf2 b !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb] :=
    free2 (free_smul _ (free_mul (free_io b _) (fxi _))) (free_zero b) (free_zero b)
      (free_mul (free_io b _) (fx _))
  have fΛ : FreeOf2 b !![1, 0; f.m L Yb, 1] := free2 (free_one b) (free_zero b) fm (free_one b)
  have fUD : FreeOf2 b (!![1, f.l L (Yb - 1); 0, 1] *
      !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb]) := by
    intro i j k l
    rw [Matrix.mul_apply]
    exact Commute.sum_right _ _ _ fun m _ => (fU i m k l).mul_right (fD m j k l)
  have hsm : star (f.m L Yb) * f.d L = f.d L * f.l L (Yb - 1) := by
    have := congrArg star hdm
    rw [star_mul, star_mul, star_star, star_d hS h] at this
    exact this
  have hΛH : (!![1, 0; f.m L Yb, 1] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![1, star (f.m L Yb); 0, 1] := by
    rw [ct2, star_one, star_zero]
  have hU : f.d L * ins b !![1, f.l L (Yb - 1); 0, 1] = star (ins b !![1, 0; f.m L Yb, 1]) * f.d L := by
    rw [Wd1.ins_star b _ fΛ, hΛH, ins2, ins2]
    simp only [mul_one, mul_zero, add_zero, mul_add, add_mul]
    rw [(fd 0 0).eq, (fd 1 1).eq, mul_assoc (eU b 0 1), hsm, ← mul_assoc, ← mul_assoc, (fd 0 1).eq]
  rw [hT, ins_conj b _ _ _ fFi, G, Wd1.ins_mul b _ _ fUD, Wd1.ins_mul b _ _ fU, h.form]
  exact asm h.F_Fi hU
end Formalism.FourierDecayAlt.P.Fr8
