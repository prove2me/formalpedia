-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.typed_local_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:19.176523+00:00
-- url     : https://prove2.me/submissions/64069214-c386-4807-9c06-4b00f311827e

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_locTyped
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_locTw
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_typedModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.TypedModel := typedModel locTw locTyped
end Formalism.FourierDecayAlt.P
