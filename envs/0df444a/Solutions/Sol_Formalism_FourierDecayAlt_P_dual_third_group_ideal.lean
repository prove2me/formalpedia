-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dual_third_group_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:33.441427+00:00
-- url     : https://prove2.me/submissions/be44711d-b018-4fde-9ea0-ba6a013f7df8

import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Dual_dual_ideal_inclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.L.DualIdealInclusion := Formalism.FourierDecayAlt.P.Dual.dual_ideal_inclusion
end Formalism.FourierDecayAlt.P
