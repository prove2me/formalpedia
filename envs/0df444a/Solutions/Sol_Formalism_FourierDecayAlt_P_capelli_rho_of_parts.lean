-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_rho_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:37.660232+00:00
-- url     : https://prove2.me/submissions/ff9bd740-0320-4e7e-ad6d-fb986f1522eb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_cvRhoOfParts


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVRhoOfParts := Formalism.FourierDecayAlt.P.JFxB.cvRhoOfParts
end Formalism.FourierDecayAlt.P
