-- Prove2me | solution 1 for Formalism.HC.HostAx.exists_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:51.722657+00:00
-- url     : https://prove2.me/submissions/9dfd614f-6f2c-4d8e-a9cd-6a255df795da

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_exists_unit_crt
import Theorems.Thm_Formalism_HC_jacobi_pred
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
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hd4 : H.d % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hd4
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.q) H.d :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left H.d H.q) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (a := H.QS * H.q) (b := H.d) rfl hc
    (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.d = (H.d - 1) % H.d := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.d : ℤ) = ((H.d - 1 : ℕ) : ℤ) % (H.d : ℤ) := by
    exact_mod_cast hu2'
  have h3 := H.der.art_ch u
  rw [jacobiSym.mod_left' h2, hj] at h3
  rcases H.art_d u hu1 with h | h
  · exfalso
    rw [h] at h3
    simp at h3
  · exact h
end Formalism.HC.HostAx
