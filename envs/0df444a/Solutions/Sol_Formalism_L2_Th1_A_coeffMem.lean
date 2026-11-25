-- Prove2me | solution 1 for Formalism.L2.Th1.A.coeffMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:03:10.1778+00:00
-- url     : https://prove2.me/submissions/74aa4507-26f5-414b-a34e-ce947b35121e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Theorems.Thm_Formalism_L2_Th1_A_coeffMem_of
import Theorems.Thm_Formalism_L2_Th1_A_halfLog
import Theorems.Thm_Formalism_L2_Th1_A_zSerMap


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
theorem _root_.solution : CoeffMem.{u} := coeffMem_of zSerMap halfLog
end Formalism.L2.Th1.A
