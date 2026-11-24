-- Prove2me | solution 1 for Formalism.BasicNotions.not_dvd_conductor_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:46:37.595825+00:00
-- url     : https://prove2.me/submissions/f541dc88-44a5-4ba7-be72-0ab062ea19f8

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_not_dvd_condN_iff_primeClass

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
variable {H}
namespace Formalism.BasicNotions
theorem _root_.solution (hp : p.Prime) (h : primeClass H p = .inertClass) : ¬ p ∣ H.condN := (not_dvd_condN_iff_primeClass H hp).2 (Or.inr (Or.inr h))
end Formalism.BasicNotions
