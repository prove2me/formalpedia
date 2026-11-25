-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_rho_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:30.366003+00:00
-- url     : https://prove2.me/submissions/12dbd1c4-f9d2-479d-9e6b-e16c767ce103

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliDetAdInvariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_cVRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho
end Formalism.FourierDecayAlt.P
