-- Prove2me | solution 1 for Formalism.BasicNotions.dvd_condN_iff_primeClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:30.295797+00:00
-- url     : https://prove2.me/submissions/93ec14a5-0b7e-4fdd-9d02-b97903e016ce

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramified_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramQ_iff
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
theorem _root_.solution (hp : p.Prime) : p ∣ H.condN ↔
    primeClass H p = .ram2 ∨ primeClass H p = .ramQ ∨ primeClass H p = .ramD := by
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨hq, hd, -, -, -⟩ := hh
  have hQS := H.QS_pos.ne'
  show p ∣ H.QS * H.q * H.d ↔ _
  rw [primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff, primeClass_eq_ramD_iff, hp.dvd_mul, hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp hq, Nat.prime_dvd_prime_iff_eq hp hd, HostRaw.small, Nat.mem_primeFactors]
  tauto
end Formalism.BasicNotions
