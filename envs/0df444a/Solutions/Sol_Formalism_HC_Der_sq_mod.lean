-- Prove2me | solution 1 for Formalism.HC.Der.sq_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:19.967808+00:00
-- url     : https://prove2.me/submissions/fdca13d9-479b-414b-bc5b-c3c86353674f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_sq_two_pow
import Theorems.Thm_Formalism_HC_Der_sq_odd_pow
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
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {d : ℤ} (hd : d % 8 = 7) (m : ℕ) (hm0 : m ≠ 0)
    (hm : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ m → jacobiSym (-d) l = 1) : ∃ s : ℤ, (m : ℤ) ∣ s ^ 2 + d := by
  revert hm0 hm
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p n hp =>
    intro _ hm
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨s, hs⟩ := sq_two_pow hd n
      exact ⟨s, by push_cast; exact (pow_dvd_pow 2 (by omega)).trans hs⟩
    · rcases n with _ | n
      · exact ⟨0, by simp⟩
      · obtain ⟨s, hs⟩ := sq_odd_pow hp hp2 (hm p hp hp2 (dvd_pow_self p (Nat.succ_ne_zero n))) n
        exact ⟨s, by push_cast; exact hs⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hm
    obtain ⟨sa, hsa⟩ := iha (by omega) (fun l hl hl2 hla => hm l hl hl2 (Dvd.dvd.mul_right hla b))
    obtain ⟨sb, hsb⟩ := ihb (by omega) (fun l hl hl2 hlb => hm l hl hl2 (Dvd.dvd.mul_left hlb a))
    have hco : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
    obtain ⟨x, y, hxy⟩ := hco
    refine ⟨sa + a * (x * (sb - sa)), ?_⟩
    push_cast
    apply IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr hab)
    · obtain ⟨k, hk⟩ := hsa
      exact ⟨k + 2 * sa * (x * (sb - sa)) + a * (x * (sb - sa)) ^ 2, by linear_combination hk⟩
    · obtain ⟨k, hk⟩ := hsb
      refine ⟨k + 2 * sb * (-y * (sb - sa)) + b * (-y * (sb - sa)) ^ 2, ?_⟩
      linear_combination hk + (sb - sa) * ((sa + a * (x * (sb - sa))) +
        (sb + b * (-y * (sb - sa)))) * hxy
end Formalism.HC.Der
