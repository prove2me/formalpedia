-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Q_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:04.580549+00:00
-- url     : https://prove2.me/submissions/f9e70467-5683-4ffb-b599-b570abcfc764

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_qProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.QProduct := Formalism.FourierDecayAlt.P.GramProductIdentities.qProduct
end Formalism.FourierDecayAlt.P
