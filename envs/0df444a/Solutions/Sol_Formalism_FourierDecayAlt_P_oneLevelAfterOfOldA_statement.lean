-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.oneLevelAfterOfOldA_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:17.08799+00:00
-- url     : https://prove2.me/submissions/6ddab29a-c64e-4eb2-b873-c5f326b67904

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_oneLevelAfterOfOldA

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.OneLevelAfterOfOldA := RecursionWithDensities.A1.oneLevelAfterOfOldA
end Formalism.FourierDecayAlt.P
