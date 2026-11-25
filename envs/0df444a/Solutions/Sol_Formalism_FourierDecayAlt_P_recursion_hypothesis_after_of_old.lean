-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.recursion_hypothesis_after_of_old
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:33.477992+00:00
-- url     : https://prove2.me/submissions/f57f4cbb-85d3-44f0-bac7-db8a4429ab49

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_J1_t_RecHypAfterOfOld

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.RecHypAfterOfOld := RecursionWithDensities.J1.t_RecHypAfterOfOld
end Formalism.FourierDecayAlt.P
