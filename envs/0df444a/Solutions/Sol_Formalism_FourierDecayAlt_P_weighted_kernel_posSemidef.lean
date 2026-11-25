-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:55.514302+00:00
-- url     : https://prove2.me/submissions/e70f258d-a41a-4221-b2bf-5846946194c4

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_weightedKernelPSD_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.WeightedKernelPSD := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightedKernelPSD_ok
end Formalism.FourierDecayAlt.P
