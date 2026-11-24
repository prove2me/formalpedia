-- Prove2me | solution 1 for Formalism.BasicNotions.primeClass_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:31.412803+00:00
-- url     : https://prove2.me/submissions/019193c3-70ac-4b2a-9a24-88dd8494031a

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramified_iff

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
theorem _root_.solution : primeClass H 2 = .ram2 := by
  apply (primeClass_eq_ramified_iff H).2
  rw [HostRaw.small, Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd, H.QS_pos.ne'⟩
end Formalism.BasicNotions
