-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.averageBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:57.922242+00:00
-- url     : https://prove2.me/submissions/50f125cd-c46c-4128-93f3-103e5335f5f2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_doubleMeanSplit
import Theorems.Thm_Formalism_FourierDecayAlt_P_partialMeansOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_orthogonalMeanNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_averageBoundOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm
end Formalism.FourierDecayAlt.P
