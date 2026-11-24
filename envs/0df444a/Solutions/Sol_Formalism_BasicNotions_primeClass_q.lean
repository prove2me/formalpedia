-- Prove2me | solution 1 for Formalism.BasicNotions.primeClass_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:11:50.498958+00:00
-- url     : https://prove2.me/submissions/3fd99669-1531-4ee5-9f7a-20272b8b9351

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramQ_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
namespace Formalism.BasicNotions
theorem _root_.solution : primeClass H H.q = .ramQ := (primeClass_eq_ramQ_iff H).2 rfl
end Formalism.BasicNotions
