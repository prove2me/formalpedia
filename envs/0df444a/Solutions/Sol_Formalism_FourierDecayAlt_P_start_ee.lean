-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.start_ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:40.294843+00:00
-- url     : https://prove2.me/submissions/ac0dbc8f-9f32-4237-bf33-afcdd15e3358

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zsub
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_bi_d56c9be81408
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Dr_Dri
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_Drbi_Drb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_comm_fns_D


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
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.StartEe := by
  intro A _ _ r L SS
  have cz := (RuleSS.comm_fns_D L (zsub L (mζ L))).1
  have czb := (RuleSS.comm_fns_D L (zsub L (mζbi L))).1
  unfold LevelData.D LevelData.Dbi
  calc L.Dr * L.ζ * (L.ζbi * L.Drbi) * (L.Drb * L.Dri * SS)
      = L.Dr * (L.ζ * L.ζbi) * (L.Drbi * L.Drb) * L.Dri * SS := by simp only [mul_assoc]
    _ = (L.ζ * L.ζbi) * (L.Dr * L.Dri) * SS := by
        rw [RuleGD.Drbi_Drb, mul_one, ← (cz.mul_left czb).eq]; simp only [mul_assoc]
    _ = L.ζ * L.ζbi * SS := by rw [RuleGD.Dr_Dri, mul_one]
end Formalism.FourierDecayAlt.P
