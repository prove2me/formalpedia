-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.oneLevelAfter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:04.159125+00:00
-- url     : https://prove2.me/submissions/42a5f67b-d300-4469-b513-84fc93ad051e

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_oneLevelAfterOfOld
import Theorems.Thm_Formalism_FourierDecayAlt_P_one_level_inequality_split_by_size


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution : OneLevelAfter := oneLevelAfterOfOld one_level_inequality_split_by_size
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
