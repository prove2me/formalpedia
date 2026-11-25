-- Prove2me | solution 1 for Formalism.HC.HostRaw.Exact.not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:23.708371+00:00
-- url     : https://prove2.me/submissions/cc1fd3e1-8b70-4eae-8cb5-af6bc4c205c3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostRam
import Theorems.Thm_Formalism_HC_Frame_TwoGroup_orderOf_GG
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_QS_dvd_condN
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
namespace Exact
theorem _root_.solution (hE : H.Exact) (h2 : φ.TwoGroup) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) : ¬ l ^ 2 ∣ H.QS := by
  intro hdvd
  obtain ⟨u, hu, hne⟩ := hE l hl ((dvd_pow_self l (by norm_num)).trans hdvd)
  obtain ⟨m, hm⟩ := hdvd.trans H.QS_dvd_condN
  have hdiv : H.condN / l = l * m := by rw [hm, sq, mul_assoc, Nat.mul_div_cancel_left _ hl.pos]
  rw [hdiv] at hu
  obtain ⟨a, ha⟩ := (Nat.modEq_iff_dvd.1 hu.symm)
  set x : ZMod H.condN := (l : ZMod H.condN) * m * a with hx
  have hN0 : (l : ZMod H.condN) ^ 2 * m = 0 := by
    have := ZMod.natCast_self H.condN
    conv_lhs at this => rw [show ((H.condN : ℕ) : ZMod H.condN) = ((l ^ 2 * m : ℕ) : ZMod H.condN) from congrArg _ hm]
    exact_mod_cast this
  have hux : (u : ZMod H.condN) = 1 + x := by
    have := congrArg (fun z : ℤ => (z : ZMod H.condN)) ha
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Nat.cast_one, Int.cast_one, Int.cast_mul,
      Nat.cast_mul] at this
    rw [hx]; linear_combination this
  have hxx : x * x = 0 := by rw [hx]; linear_combination (m * a * a : ZMod H.condN) * hN0
  have hpow : ∀ n : ℕ, (1 + x) ^ n = 1 + n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih]; push_cast; linear_combination (n : ZMod H.condN) * hxx
  have hul : u ^ l = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hux, hpow, Units.val_one, hx]
    linear_combination (a : ZMod H.condN) * hN0
  have h3 : orderOf (H.art u) ∣ l := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hul, map_one])
  obtain ⟨i, hi⟩ := h2.orderOf_GG (H.art u)
  rcases (Nat.dvd_prime hl).1 h3 with h | h
  · exact hne (orderOf_eq_one_iff.1 h)
  · rw [hi] at h
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h.symm.dvd))
end Exact
end Formalism.HC.HostRaw
