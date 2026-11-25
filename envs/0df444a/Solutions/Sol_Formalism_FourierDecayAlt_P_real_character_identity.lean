-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.real_character_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:25.454871+00:00
-- url     : https://prove2.me/submissions/6269dd73-8039-483e-b9c2-f11c296b4080

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_realCharacter_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.RealCharacter := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realCharacter_ok
end Formalism.FourierDecayAlt.P
