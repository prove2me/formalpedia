-- Prove2me | solution 1 for Formalism.BasicNotions.Host.dvd_condN_iff_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:11:47.74655+00:00
-- url     : https://prove2.me/submissions/96c563d0-3273-47b4-bf39-ad093c00bdb7

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_DvdCondNIffCls
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    p ∣ H.condN ↔ H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD := by
  have key : H.cls p = .ram2 ∨ H.cls p = .ramQ ∨ H.cls p = .ramD ↔ p ∈ H.small ∨ p = H.q ∨ p = H.d := by
    unfold Host.cls primeClass
    split_ifs <;> simp_all
  obtain ⟨hqp, hdp, -, -, -⟩ := H.hyp
  have hQS : H.QS ≠ 0 := H.QS_pos.ne'
  have hs : p ∣ H.QS ↔ p ∈ H.small := by
    show p ∣ H.QS ↔ p ∈ H.QS.primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨hp, h, hQS⟩, fun h => h.2.1⟩
  rw [key, show H.condN = H.QS * H.q * H.d from rfl, hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp hqp,
    Nat.prime_dvd_prime_iff_eq hp hdp, hs, or_assoc]
end Formalism.BasicNotions.Host
