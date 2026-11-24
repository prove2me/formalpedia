-- Prove2me | solution 1 for Formalism.L2.Host.algC_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:28.13052+00:00
-- url     : https://prove2.me/submissions/3b4c0a85-c14c-41d0-934a-b97e1cf3557c

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Host
namespace Formalism.L2.Host
theorem _root_.solution (ι : Qb →+* ℂ) (x : Qb) : ((algC ι x : algebraicClosure ℚ ℂ) : ℂ) = ι x := rfl
end Formalism.L2.Host
