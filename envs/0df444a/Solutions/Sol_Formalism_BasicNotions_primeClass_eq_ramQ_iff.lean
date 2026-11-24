-- Prove2me | solution 1 for Formalism.BasicNotions.primeClass_eq_ramQ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:19.961645+00:00
-- url     : https://prove2.me/submissions/1ca49174-bcbe-404b-9c98-6accf09f8e58

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
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


section
open NumberField Formalism.FrobeniusOrbits Formalism.HC
namespace Formalism.BasicNotions
section cls
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
private theorem ne_q_and_ne_d_of_mem_small (hp : p ∈ H.small) : p ≠ H.q ∧ p ≠ H.d := by
  rw [HostRaw.small, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hdvd, -⟩ := hp
  have hc := H.QS_coprime
  constructor
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.q ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_right _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  · intro heq
    rw [heq] at hdvd hpp
    have h1 : H.d ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdvd (dvd_mul_left _ _)
    rw [hc.gcd_eq_one] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
variable {H}
end cls
namespace Ranks
variable (R : Ranks)
end Ranks
namespace Host
variable {R : Ranks} (H : Host R)
end Host
end Formalism.BasicNotions
end

set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
namespace Formalism.BasicNotions
theorem _root_.solution : primeClass H p = .ramQ ↔ p = H.q := by
  have hs : p ∈ H.small → p ≠ H.q := fun h => (ne_q_and_ne_d_of_mem_small H h).1
  unfold primeClass
  split_ifs <;> simp_all
end Formalism.BasicNotions
