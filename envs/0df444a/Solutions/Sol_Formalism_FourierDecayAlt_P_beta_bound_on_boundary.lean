-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.beta_bound_on_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:03.764835+00:00
-- url     : https://prove2.me/submissions/8b8e1ff5-06ee-406e-87ed-602d2bde2731

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_betaOnCut_of_tcritLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_critical_threshold_lower_bound


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
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.BetaOnCut := Sz7.betaOnCut_of_tcritLower critical_threshold_lower_bound
end Formalism.FourierDecayAlt.P
