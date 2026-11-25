-- Prove2me | solution 1 for Formalism.L2.Th1.A.uSerEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:36.501377+00:00
-- url     : https://prove2.me/submissions/e6bde9c8-bd5c-4268-856e-8da1729abc5e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Theorems.Thm_Formalism_L2_Th1_A_uSerEq_of
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
theorem _root_.solution : USerEq := uSerEq_of wpShape wpRecursion
end Formalism.L2.Th1.A
