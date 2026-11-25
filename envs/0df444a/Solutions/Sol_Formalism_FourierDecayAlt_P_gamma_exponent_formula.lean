-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gamma_exponent_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:45:17.60675+00:00
-- url     : https://prove2.me/submissions/e4a7eb31-433e-4236-af5b-b3ec427acf34

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_gaExponent_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.GaExponent := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok
end Formalism.FourierDecayAlt.P
