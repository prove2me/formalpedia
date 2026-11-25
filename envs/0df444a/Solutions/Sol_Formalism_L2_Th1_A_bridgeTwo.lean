-- Prove2me | solution 1 for Formalism.L2.Th1.A.bridgeTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:41.732163+00:00
-- url     : https://prove2.me/submissions/2a00c715-8798-4d5b-83ab-11cf713979a1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Theorems.Thm_Formalism_L2_Th1_A_twoTorsionZ
import Theorems.Thm_Formalism_L2_Th1_A_tInZ
import Theorems.Thm_Formalism_L2_Th1_A_bridgeTwo_of
import Theorems.Thm_Formalism_L2_Th1_A_coeffMem


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
theorem _root_.solution : BridgeTwo := bridgeTwo_of coeffMem tInZ twoTorsionZ
end Formalism.L2.Th1.A
