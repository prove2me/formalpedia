-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ee_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:24:58.736805+00:00
-- url     : https://prove2.me/submissions/64f363bd-1f20-4259-9306-2eaf7a22b555

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_i_b8c0bb40777f
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_l0_mul_gg_eq_gg_mul_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_eeConj_abs
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_hat___e058134a6d5d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_commute_x_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_divided_difference_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps
import Theorems.Thm_Formalism_YangianSpanCharacter_P_wedgeMapInLieAlgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.EeConj := by
  intro A S _ _ _ _ _ _ r L f Y Ya hf hY hY1 hYa hYa1 hne
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f hf
  have y1 := Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra ℂ (SlopeTestRemainingChoices S A) f.hatT (fun Y => io L.GGi * f.xi Y) f.hatQ f.inv H Ya Y hYa hY
    hne.symm
  have hη := divided_difference_l A S r L f Ya Y hne.symm
  have hDD : f.DD Ya Y = f.DD Y Ya := by
    unfold FrameData.DD
    rw [← neg_sub Y Ya, ← neg_sub (f.ee Y) (f.ee Ya), inv_neg, smul_neg, neg_smul, neg_neg]
  unfold eta at y1
  rw [Hl Y hY hY1, Hl Ya hYa hYa1, hη, hat_τ hf (hf.inv_reg hYa), hDD] at y1
  unfold FrameData.l at y1
  refine eeConj_abs (io L.GG) (io L.GGi) (f.x Ya) (f.xi Ya) (io (L.l0 Y)) (io (L.ζb * L.GGi)) (kapL L)
    (io (L.GG * L.ζ * L.ζbi)) (f.ee Y) (f.DD Y Ya) ?_ ?_ (hf.x_xi Ya hYa).2 ?_ (commute_x_l0 hf Ya Y) ?_ ?_ ?_
    (hf.ee_fn Y _ (mGG L)) y1
  · rw [← io_mul, L.GGi_GG, io_one]
  · unfold kapL
    rw [← io_mul]
    have e : L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi) = 1 := by
      calc L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi)
          = L.GG * (L.ζ * ((L.ζbi * L.ζb) * L.ζi)) * L.GGi := by simp only [mul_assoc]
        _ = 1 := by rw [L.ζbi_ζb, one_mul, L.ζ_ζi, mul_one, L.GG_GGi]
    rw [e, io_one]
  · rw [← io_mul, l0_mul_gg_eq_gg_mul_sub, io_mul]; simp only [io, map_sub]
  · rw [io_mul]; exact (hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mGGi L))
  · unfold kapL; rw [io_mul, io_mul]
    exact ((hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mζi L))).mul_right (hf.x_fn Ya _ (mGGi L))
  · exact io_comm (((zc L (mζb L) (mGG L)).mul_left (zc L (mζi L) (mGG L))).mul_left (zc L (mGGi L) (mGG L)))
end Formalism.FourierDecayAlt.P
