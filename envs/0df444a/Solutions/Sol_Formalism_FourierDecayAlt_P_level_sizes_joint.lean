-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_sizes_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:24.542513+00:00
-- url     : https://prove2.me/submissions/1ab4b70f-f948-4d2e-925c-1e1b88c03a8d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_LevelSizesJoint

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.LevelSizesJoint := Jx2.t_LevelSizesJoint
end Formalism.FourierDecayAlt.P
