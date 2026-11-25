-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_Q_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:44:30.288425+00:00
-- url     : https://prove2.me/submissions/646edfc8-b53b-43cb-9c16-9c4241e020cd

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_lemmaQOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.LemmaQOfParts := Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQOfParts
end Formalism.FourierDecayAlt.P
