-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:50.908476+00:00
-- url     : https://prove2.me/submissions/bd5fade3-1f82-4860-9fcb-1edfe2e7200a

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_gramSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.GramSum := Formalism.FourierDecayAlt.P.GramProductIdentities.gramSum
end Formalism.FourierDecayAlt.P
