-- Prove2me | solution 1 for Formalism.HC.HostRaw.ordCompl_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:12.504794+00:00
-- url     : https://prove2.me/submissions/3079bfbd-89be-4970-9a44-9ecf886c243c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_ordCompl_mul_prime
import Theorems.Thm_Formalism_HC_HostRaw_condN_eq_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : ordCompl[H.q] H.condN = H.QS * H.d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  rw [condN_eq_q]
  apply ordCompl_mul_prime hq
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  exact Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd
end Formalism.HC.HostRaw
