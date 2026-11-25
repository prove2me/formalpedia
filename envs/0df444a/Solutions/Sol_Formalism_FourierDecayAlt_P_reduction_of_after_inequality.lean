-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reduction_of_after_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:26.065028+00:00
-- url     : https://prove2.me/submissions/00c41f94-617c-4ea4-9bda-8e9a5cd228fa

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A2_reductionOfAfter

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.ReductionOfAfter := RecursionWithDensities.A2.reductionOfAfter
end Formalism.FourierDecayAlt.P
