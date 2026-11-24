-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_adjoint_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:41:05.627151+00:00
-- url     : https://prove2.me/submissions/2123dac8-5e8b-4fbe-8f6a-53703b0437cc

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_hat_apply
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_hat___e058134a6d5d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_d_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_di_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_hat_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_adjoint_l_shift_relation
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.FrameM := by
  intro A S _ _ _ _ _ _ r L f Y hL hf hr hY hYm
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f hf
  have hr' : star (Y - 1) = Y - 1 := by rw [star_sub, hr, star_one]
  have hY' : Y - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have adj := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT (fun Y => io L.GGi * f.xi Y) f.hatQ f.inv (f.d L) H
    (d_star hL hf) (Y - 1) hYm hY' (hat_herm hf (hf.inv_reg hYm) hr')
  rw [Hl (Y - 1) hYm hY', sub_add_cancel] at adj
  have hm : mf f.hatT (fun Y => io L.GGi * f.xi Y) Y = f.m L Y := by
    unfold FrameData.m
    rw [mul_assoc, ← adj, ← mul_assoc, di_d hf, one_mul]
  have hτ : io L.GG * f.x Y * (io L.GGi * f.xi Y) = 1 := by
    have := (H.2.2.2.1 Y hY).1
    rwa [hat_τ hf (hf.inv_reg hY)] at this
  rw [← hm]
  unfold mf
  rw [← mul_assoc (io L.GG * f.x Y), hτ, one_mul, hat_apply (hf.inv_reg hY), mul_assoc, hf.Fi_F, mul_one]
end Formalism.FourierDecayAlt.P
