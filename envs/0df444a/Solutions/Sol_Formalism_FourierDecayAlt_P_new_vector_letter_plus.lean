-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.new_vector_letter_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:45.243011+00:00
-- url     : https://prove2.me/submissions/2e49f2cd-7a80-4143-a486-a947514ce990

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_i_b8c0bb40777f
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Drbi_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Dri_Dr


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
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.NewLetterPlus := by
  intro A S _ _ _ _ _ _ r L f Y hee
  have a1 : L.Di * L.Ahat Y = L.ζi * L.Ar Y := by
    unfold LevelData.Di LevelData.Ahat
    rw [mul_assoc, ← mul_assoc L.Dri, RuleGD.Dri_Dr, one_mul]
  have a2 : L.Dbi * L.R0 Y = L.ζbi * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) := by
    unfold LevelData.Dbi LevelData.R0
    simp only [mul_assoc]; rw [← mul_assoc L.Drbi, RuleGD.Drbi_Drb, one_mul]
  have k0 : L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζi := by
    calc L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζbi * (L.GG * (L.ζb * L.ζi)) * L.GGi := by
          simp only [mul_assoc]
      _ = L.ζbi * ((L.ζb * L.ζi) * L.GG) * L.GGi := by
          rw [((zc L (mGG L) (mζb L)).mul_right (zc L (mGG L) (mζi L))).eq]
      _ = (L.ζbi * L.ζb) * L.ζi * (L.GG * L.GGi) := by simp only [mul_assoc]
      _ = L.ζi := by rw [L.ζbi_ζb, L.GG_GGi, one_mul, mul_one]
  have k : (io L.ζbi : SlopeTestRemainingChoices S A) * io L.GG * kapL L = io L.ζi := by
    unfold kapL; rw [← io_mul, ← io_mul, k0]
  have key : (io L.ζbi : SlopeTestRemainingChoices S A) * (io L.GG * f.l L Y) * io (L.Ar Y) + io L.ζbi * io L.GG * io (L.Br Y) =
      io L.ζbi * io L.GG * (io (L.l0 Y) * io (L.Ar Y) + io (L.Br Y)) +
        f.ee Y * (io L.ζi * io (L.Ar Y)) := by
    unfold FrameData.l
    calc (io L.ζbi : SlopeTestRemainingChoices S A) * (io L.GG * (io (L.l0 Y) + kapL L * f.ee Y)) * io (L.Ar Y) +
          io L.ζbi * io L.GG * io (L.Br Y)
        = io L.ζbi * io L.GG * (io (L.l0 Y) * io (L.Ar Y) + io (L.Br Y)) +
          (io L.ζbi * io L.GG * kapL L) * f.ee Y * io (L.Ar Y) := by noncomm_ring
      _ = _ := by rw [k, ← (hee _ (mζi L)).eq, mul_assoc (f.ee Y)]
  ext1 i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, a1, io_mul]
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, a1, a2, io_mul, io_add] using key
end Formalism.FourierDecayAlt.P
