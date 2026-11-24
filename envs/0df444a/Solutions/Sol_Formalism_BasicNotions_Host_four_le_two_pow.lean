-- Prove2me | solution 1 for Formalism.BasicNotions.Host.four_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:21.293794+00:00
-- url     : https://prove2.me/submissions/790f0214-3bac-4ae2-8142-7dbbd57ba9b5

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls

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
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H
namespace Formalism.BasicNotions.Host
theorem _root_.solution : 4 ≤ 2 ^ R.e := by
  have h := H.two_le_e
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ R.e := Nat.pow_le_pow_right (by norm_num) h
end Formalism.BasicNotions.Host
