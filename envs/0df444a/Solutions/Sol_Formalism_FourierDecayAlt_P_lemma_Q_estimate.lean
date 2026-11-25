-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_Q_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:44:24.141289+00:00
-- url     : https://prove2.me/submissions/b510e6d6-8938-4143-96e9-66efaa520f67

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_lemmaQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.LemmaQ := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQ
end Formalism.FourierDecayAlt.P
