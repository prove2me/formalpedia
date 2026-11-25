-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_orbit_of_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:52.551874+00:00
-- url     : https://prove2.me/submissions/480fd796-9cd1-4ad5-8d97-a66a66982d11

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_big_cell_orbit_set


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.GqOmOfDom := fun _ => Formalism.FourierDecayAlt.P.big_cell_orbit_set
end Formalism.FourierDecayAlt.P
