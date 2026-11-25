-- Prove2me | solution 1 for Formalism.HC.EvenGrp.twoGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:53.260014+00:00
-- url     : https://prove2.me/submissions/bcb4632f-6726-4562-a4ef-6e08aee79c34

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_card_B
import Theorems.Thm_Formalism_HC_D7_ord_eq
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_EvenData_ord_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
namespace Formalism.HC.EvenGrp
theorem _root_.solution (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e hev).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  have hU : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
      show e + 2 - 1 = e + 1 by omega]
    norm_num
  have h2 : Nat.card (HGrp e) ∣ 2 ^ (e + 1) := by
    have h0 := Subgroup.card_quotient_dvd_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
    rwa [hU] at h0
  have hB : Nat.card (B Ξ) = 2 ^ j := (card_B Ξ).trans hj
  have h3 : Nat.card (data Ξ e hev).R ∣ 2 ^ (e + 1 + j) := by
    have h1 : Nat.card (data Ξ e hev).R ∣ Nat.card (HGrp e × B Ξ) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_prod, hB] at h1
    rw [pow_add]
    exact h1.trans (mul_dvd_mul_right h2 _)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  exact ⟨k, ((data Ξ e hev).ord_eq).trans hk⟩
end Formalism.HC.EvenGrp
