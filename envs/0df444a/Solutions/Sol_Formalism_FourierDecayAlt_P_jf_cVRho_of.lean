-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_cVRho_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:30:11.323422+00:00
-- url     : https://prove2.me/submissions/b62506f9-8c5c-430f-a1e9-7a84016f3469

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRho_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxB.CapAdInv → Formalism.FourierDecayAlt.JF.CVRho :=
  fun hA => Formalism.FourierDecayAlt.P.JFxB.cvRho_of hA
end Formalism.FourierDecayAlt.P
