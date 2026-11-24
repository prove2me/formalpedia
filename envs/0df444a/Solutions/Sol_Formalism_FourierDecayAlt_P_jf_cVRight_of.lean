-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_cVRight_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:34:01.654742+00:00
-- url     : https://prove2.me/submissions/76d911a2-3b76-48aa-8e2d-fd67923d08f6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRight_of


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
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxB.CapAdInv → Formalism.FourierDecayAlt.JF.CVRight :=
  fun hA => Formalism.FourierDecayAlt.P.JFxB.cvRight_of hA
end Formalism.FourierDecayAlt.P
