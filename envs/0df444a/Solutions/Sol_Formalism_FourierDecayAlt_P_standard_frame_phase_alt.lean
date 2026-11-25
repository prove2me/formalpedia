-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.standard_frame_phase_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:54:02.658172+00:00
-- url     : https://prove2.me/submissions/89ad242e-dff3-438a-94ea-b65101e821b2

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_stdFramePhase_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.StdFramePhase := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.stdFramePhase_ok
end Formalism.FourierDecayAlt.P
