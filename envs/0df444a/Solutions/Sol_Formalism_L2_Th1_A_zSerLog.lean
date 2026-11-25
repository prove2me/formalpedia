-- Prove2me | solution 1 for Formalism.L2.Th1.A.zSerLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:47.448554+00:00
-- url     : https://prove2.me/submissions/3894bae7-6174-4ed9-9b4d-7264a1363fe8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Theorems.Thm_Formalism_L2_Th1_A_fglLog
import Theorems.Thm_Formalism_L2_Th1_A_zSerLog_of


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
theorem _root_.solution : ZSerLog.{u} := zSerLog_of fglLog
end Formalism.L2.Th1.A
