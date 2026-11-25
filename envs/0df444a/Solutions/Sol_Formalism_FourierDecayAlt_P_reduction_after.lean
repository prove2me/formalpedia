-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reduction_after
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:52.622904+00:00
-- url     : https://prove2.me/submissions/f4e973b0-e3b2-43e3-887f-54fa15213992

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_oneLevelAfterA
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A2_reductionAfterOfSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_domination_limit
import Theorems.Thm_Formalism_FourierDecayAlt_P_epsilon_limit
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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.ReductionAfter := RecursionWithDensities.A2.reductionAfterOfSteps RecursionWithDensities.A1.oneLevelAfterA epsilon_limit domination_limit joint_theorem_A'
end Formalism.FourierDecayAlt.P
