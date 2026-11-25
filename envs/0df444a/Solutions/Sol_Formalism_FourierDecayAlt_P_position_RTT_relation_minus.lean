-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_RTT_relation_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:00.811569+00:00
-- url     : https://prove2.me/submissions/4fcd96db-95f4-4f06-b5a9-1fd9644a24ad

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_rtt_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_position_minus_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.PositionRTTMinus := by
  intro K A S _ _ _ _ _ _ _ _ b M N d hM hN H
  unfold Rht0
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    Formalism.FourierDecayAlt.P.Wd2.position_minus_core b M N d hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry N M d H)]
end Formalism.FourierDecayAlt.P
