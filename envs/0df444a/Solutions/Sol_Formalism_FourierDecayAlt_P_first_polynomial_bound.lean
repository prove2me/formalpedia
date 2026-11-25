-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:31.313067+00:00
-- url     : https://prove2.me/submissions/712c2e5d-0893-417e-821d-4bca184dc42c

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_p1aBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.CauchySchwarzInvariantForm := Formalism.FourierDecayAlt.P.GramProductIdentities.p1aBound
end Formalism.FourierDecayAlt.P
