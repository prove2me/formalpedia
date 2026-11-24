-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theorem_a_after
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:26.90598+00:00
-- url     : https://prove2.me/submissions/7ec85d02-14bf-4dfd-a9a1-9b8c0d9ef8ee

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_oneLevelAfter
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B2_theoremAAfterOfSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_limitStep
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_joint_theorem_A__e6b3bc7ee1c6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open RecursionWithDensities
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TC.TheoremAAfter := RecursionWithDensities.B2.theoremAAfterOfSteps RecursionWithDensities.B1.oneLevelAfter limitStep joint_theorem_A'
end Formalism.FourierDecayAlt.P
