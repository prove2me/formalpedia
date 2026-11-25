-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_jacobian_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:37.076815+00:00
-- url     : https://prove2.me/submissions/a5cfaa21-0b63-40db-b73e-e0fed95f98fa

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_frameJacobian_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.FrameJacobian := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameJacobian_ok
end Formalism.FourierDecayAlt.P
