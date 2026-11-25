-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_left_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:28:28.650478+00:00
-- url     : https://prove2.me/submissions/f009fe39-3fbb-4469-8eaf-a0c2307f5a02

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvLeft


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVLeft := Formalism.FourierDecayAlt.P.JFxB.cvLeft
end Formalism.FourierDecayAlt.P
