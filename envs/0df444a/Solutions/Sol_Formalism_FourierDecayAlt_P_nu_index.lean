-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nu_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:45.456481+00:00
-- url     : https://prove2.me/submissions/6109c42a-46d6-47fb-8c36-0d13cd49d338

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_NuIndex

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.NuIndex := Jx2.t_NuIndex
end Formalism.FourierDecayAlt.P
