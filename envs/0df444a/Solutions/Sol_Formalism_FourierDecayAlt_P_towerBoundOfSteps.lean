-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.towerBoundOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:41.016123+00:00
-- url     : https://prove2.me/submissions/429417f1-3d59-4ecc-a37b-54134cdc01fa

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_theoremA_of_steps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.TheoremAOfSteps := OneLevelCoefficients.theoremA_of_steps
end Formalism.FourierDecayAlt.P
