-- Prove2me | solution 1 for Formalism.HC.HostRaw.PsQ.exists_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:47.397107+00:00
-- url     : https://prove2.me/submissions/a1d1087c-fcc7-4604-8d3b-2ffe8d2eeeba

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_exists_unit_crt
import Theorems.Thm_Formalism_HC_jacobi_pred
import Theorems.Thm_Formalism_HC_HostRaw_condN_eq_q
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
variable {H}
namespace Formalism.HC.HostRaw
namespace PsQ
theorem _root_.solution (hP : H.PsQ) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hq4 : H.q % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hq4
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.d) H.q :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (condN_eq_q H) hc (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.q = (H.q - 1) % H.q := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.q : ℤ) = ((H.q - 1 : ℕ) : ℤ) % (H.q : ℤ) := by
    exact_mod_cast hu2'
  have h3 : (((H.art u).1.1 : ℤˣ) : ℤ) = -1 := by
    rw [hP u, jacobiSym.mod_left' h2, hj]
  exact Units.ext (by simpa using h3)
end PsQ
end Formalism.HC.HostRaw
