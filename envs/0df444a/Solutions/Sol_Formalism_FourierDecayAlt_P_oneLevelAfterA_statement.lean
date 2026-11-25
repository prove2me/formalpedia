-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.oneLevelAfterA_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:56.6608+00:00
-- url     : https://prove2.me/submissions/6c81d9a2-d2de-4a2c-9ad9-5c34134a0ae6

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_oneLevelAfterA

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.OneLevelAfterA := RecursionWithDensities.A1.oneLevelAfterA
end Formalism.FourierDecayAlt.P
