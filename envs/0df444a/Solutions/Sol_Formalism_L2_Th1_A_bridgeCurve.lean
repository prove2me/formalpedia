-- Prove2me | solution 1 for Formalism.L2.Th1.A.bridgeCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:02.075293+00:00
-- url     : https://prove2.me/submissions/6ac86a34-6688-48ec-95d4-f91e6c958654

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Theorems.Thm_Formalism_L2_Th1_A_wpInU
import Theorems.Thm_Formalism_L2_Th1_A_bridgeCurve_of
import Theorems.Thm_Formalism_L2_Th1_A_coeffMem
import Theorems.Thm_Formalism_L2_Th1_A_cubeTwoR


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
theorem _root_.solution : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR
end Formalism.L2.Th1.A
