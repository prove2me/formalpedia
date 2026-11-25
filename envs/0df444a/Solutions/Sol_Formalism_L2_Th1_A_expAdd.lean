-- Prove2me | solution 1 for Formalism.L2.Th1.A.expAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:19.462615+00:00
-- url     : https://prove2.me/submissions/f9eb869c-b936-426a-82b2-4d97580123f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_ChordEquation
import Theorems.Thm_Formalism_L2_Th1_A_expSeriesAdd


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
theorem _root_.solution : ExpAdd.{u} := expSeriesAdd
end Formalism.L2.Th1.A
