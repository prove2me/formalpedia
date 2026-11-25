-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.scaling_beta_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:48.916946+00:00
-- url     : https://prove2.me/submissions/9ab5d94b-25c6-4b04-a9f3-674bd0d3b3e2

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_scaleBeta_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleBeta := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.scaleBeta_ok
end Formalism.FourierDecayAlt.P
