-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.real_frame_entry_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:29.78104+00:00
-- url     : https://prove2.me/submissions/17019cc6-5428-42dc-b14f-fb5781dbdc1c

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_realFrameEntry_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.RealFrameEntry := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realFrameEntry_ok
end Formalism.FourierDecayAlt.P
