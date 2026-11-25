-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpNumEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:41.7128+00:00
-- url     : https://prove2.me/submissions/a4a916e1-e279-4877-b2a0-b72544baad6f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Theorems.Thm_Formalism_L2_Th1_A_wpNumEq_of
import Theorems.Thm_Formalism_L2_Th1_A_wpRecursion
import Theorems.Thm_Formalism_L2_Th1_A_wpShape


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : WpNumEq := wpNumEq_of wpShape wpRecursion
end Formalism.L2.Th1.A
