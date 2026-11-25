-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_cVUnderInt_of_jDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:18.651909+00:00
-- url     : https://prove2.me/submissions/8f8e0666-4be1-4363-a3f5-b5d8be3b554e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliDetAdInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvUnderInt_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvWordSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_words_of_domain
import Theorems.Thm_Formalism_FourierDecayAlt_P_rewrite_rho_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.CVUnderInt := by
  intro hD
  exact Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of (Formalism.FourierDecayAlt.P.bessel_words_of_domain hD) Formalism.FourierDecayAlt.P.JFxB.cvWordSum
    Formalism.FourierDecayAlt.P.rewrite_rho_action
end Formalism.FourierDecayAlt.P
