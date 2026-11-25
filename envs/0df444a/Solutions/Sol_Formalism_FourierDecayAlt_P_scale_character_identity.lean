-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.scale_character_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:27.08679+00:00
-- url     : https://prove2.me/submissions/db43d3e2-bb90-4b7c-9451-a0f11c9a8499

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScaleThresholdCharacters_scaleCharacter_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleCharacter := Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleCharacter_ok
end Formalism.FourierDecayAlt.P
