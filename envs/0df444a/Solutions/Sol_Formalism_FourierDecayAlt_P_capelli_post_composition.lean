-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_post_composition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:34.014128+00:00
-- url     : https://prove2.me/submissions/40d43ffb-3914-45fa-a6dd-def5f437f67c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvPost


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVPost := Formalism.FourierDecayAlt.P.JFxB.cvPost
end Formalism.FourierDecayAlt.P
