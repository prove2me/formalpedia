-- Prove2me | solution 1 for Formalism.HC.EvenGrp.exact_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:07.163709+00:00
-- url     : https://prove2.me/submissions/1b02aa23-d2dd-45df-955f-b7877746dd19

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_unitsMap_unitOfCoprime
import Theorems.Thm_Formalism_HC_EvenGrp_not_good
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_eq_hcl_iff
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_unitsMap_val_modEq
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
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
namespace Formalism.HC.EvenGrp
theorem _root_.solution (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e hev).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega
end Formalism.HC.EvenGrp
