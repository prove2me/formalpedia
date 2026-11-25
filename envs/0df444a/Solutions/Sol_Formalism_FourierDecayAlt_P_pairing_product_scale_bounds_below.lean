-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.pairing_product_scale_bounds_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:20.783034+00:00
-- url     : https://prove2.me/submissions/9cb82f96-b576-453b-aec4-bc6cce52f66e

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScaleThresholdCharacters_scaleThresholdsBelow_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsBelow := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsBelow_ok
end Formalism.FourierDecayAlt.P
