-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.truncation_room_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:47.97285+00:00
-- url     : https://prove2.me/submissions/e30a7a86-fc6c-4ad1-b7c5-6049ba3771ff

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_cutRoom_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.CutRoom := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.cutRoom_ok
end Formalism.FourierDecayAlt.P
