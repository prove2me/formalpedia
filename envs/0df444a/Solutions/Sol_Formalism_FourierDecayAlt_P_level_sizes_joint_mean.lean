-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_sizes_joint_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:28.749324+00:00
-- url     : https://prove2.me/submissions/6ec586fe-f2d4-4c7b-8755-ba93fee7b9ce

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_LevelSizesJointMean

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.LevelSizesJointMean := Jx2.t_LevelSizesJointMean
end Formalism.FourierDecayAlt.P
