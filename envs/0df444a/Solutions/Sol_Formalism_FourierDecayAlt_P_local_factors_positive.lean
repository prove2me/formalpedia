-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_factors_positive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:14.356605+00:00
-- url     : https://prove2.me/submissions/5b60703c-6587-4d07-bc75-72bbca01635d

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameIntegralJacobian_factorsPositive_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.FactorsPositive := Formalism.FourierDecayAlt.P.FrameIntegralJacobian.factorsPositive_ok
end Formalism.FourierDecayAlt.P
