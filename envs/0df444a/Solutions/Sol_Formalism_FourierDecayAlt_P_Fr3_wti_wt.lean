-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.wti_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:57.346793+00:00
-- url     : https://prove2.me/submissions/32e4e782-f1d0-4f12-8683-fd7f1456664e

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  have e : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
    calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi)
        = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by simp only [mul_assoc]
      _ = L.GG * L.ζi * (L.ζ * L.ζbi) * L.ζb * L.GGi := by rw [(zc L (mζbi L) (mζ L)).eq]
      _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by simp only [mul_assoc]
      _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]
  unfold wti wt
  rw [← io_mul, e, io_one]
end Formalism.FourierDecayAlt.P.Fr3
