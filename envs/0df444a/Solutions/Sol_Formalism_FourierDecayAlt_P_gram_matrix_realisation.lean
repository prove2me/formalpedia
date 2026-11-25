-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_matrix_realisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:41.683985+00:00
-- url     : https://prove2.me/submissions/74fc12c8-3ee9-48f9-bb23-9b86b811b8a3

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_gramRealise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.GramRealise := Formalism.FourierDecayAlt.P.GramProductIdentities.gramRealise
end Formalism.FourierDecayAlt.P
