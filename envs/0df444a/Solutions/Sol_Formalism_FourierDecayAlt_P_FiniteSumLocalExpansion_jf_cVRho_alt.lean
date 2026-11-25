-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.jf_cVRho_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:46.325903+00:00
-- url     : https://prove2.me/submissions/e6c49f8f-2483-41cc-9386-49005561ed8a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_capAdInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_cVRho_of


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
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution : Formalism.FourierDecayAlt.JF.CVRho := Formalism.FourierDecayAlt.P.jf_cVRho_of Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
