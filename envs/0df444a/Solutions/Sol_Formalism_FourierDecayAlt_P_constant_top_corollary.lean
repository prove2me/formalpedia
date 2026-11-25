-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.constant_top_corollary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:40.069696+00:00
-- url     : https://prove2.me/submissions/24c17821-bc5f-4dae-9688-d79d4ae43096

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScaleThresholdCharacters_corAConstTop_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstTop := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAConstTop_ok
end Formalism.FourierDecayAlt.P
