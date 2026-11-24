-- Prove2me | solution 1 for Formalism.BasicNotions.primeClass_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:51:15.940196+00:00
-- url     : https://prove2.me/submissions/bd483072-6fb3-4a08-95f9-84325cc58103

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramD_iff

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
theorem _root_.solution : primeClass H H.d = .ramD := (primeClass_eq_ramD_iff H).2 rfl
end Formalism.BasicNotions
