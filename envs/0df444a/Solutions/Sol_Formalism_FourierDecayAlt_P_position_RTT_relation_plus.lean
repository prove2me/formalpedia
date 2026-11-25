-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_RTT_relation_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:08.4703+00:00
-- url     : https://prove2.me/submissions/515aecd4-1337-46af-84fc-1d07800c2480

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_rtt_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_position_plus_core

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
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.PositionRTTPlus := by
  intro K A S _ _ _ _ _ _ _ _ a M N D hM hN H
  unfold Rh0
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    Formalism.FourierDecayAlt.P.Wd2.position_plus_core a M N D hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry M N D H)]
end Formalism.FourierDecayAlt.P
