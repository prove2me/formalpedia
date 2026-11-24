-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:58:58.765054+00:00
-- url     : https://prove2.me/submissions/9e9cb128-b76d-433d-8977-71c574c1d895

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_ind
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_neg_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_order_le
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_order_le_card
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_hcl_pow_eq_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_odd_of_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostOrders := by
  unfold HostOrders
  intro e
  refine ⟨fun j l u hu => ?_, ?_⟩
  · have hl : Odd l := odd_of_unit e l u hu
    have h1 : u ^ (2 ^ j) = 1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_one, Int.cast_pow]
    have h2 : u ^ (2 ^ j) = -1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_neg, Units.val_one, Int.cast_pow]
    rcases Nat.lt_or_ge (e + 1) j with hj | hj
    · simp only [cast_eq_one, cast_eq_neg_one]
      rw [show e + 2 - j = 0 by omega]
      simp only [pow_zero, Nat.cast_one, one_dvd, or_self, iff_true]
      exact (order_le_card e _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [order_le, hcl_pow_eq_one, h1, h2]
      simp only [cast_eq_one, cast_eq_neg_one]
      push_cast
      obtain ⟨M, hM⟩ : ∃ M, e + 2 = M + j := ⟨e + 2 - j, by omega⟩
      rw [hM, show M + j - j = M by omega]
      exact ind l hl M (by omega) j
  · unfold GG cc G0 c0
    have hne : (-1 : ℤˣ) ≠ 1 := by
      first
        | decide
        | (intro h; have h' := congrArg Units.val h; norm_num at h')
    intro g
    constructor
    · rw [Subgroup.mem_zpowers_iff]
      rintro ⟨k, hk⟩
      have hk1 : g.1.1 ^ k = -1 := congrArg (fun x => x.1.1) hk
      have hk2 : g.1.2 ^ k = -1 := congrArg (fun x => x.1.2) hk
      have hk3 : g.2 ^ k = 1 := congrArg (fun x => x.2) hk
      have hodd : Odd k := by
        rcases Int.even_or_odd k with he | ho
        · exfalso
          rcases Int.units_eq_one_or g.1.1 with h1 | h1
          · rw [h1, one_zpow] at hk1
            exact hne hk1.symm
          · rw [h1, he.neg_one_zpow] at hk1
            exact hne hk1.symm
        · exact ho
      have hu : ∀ v : ℤˣ, v ^ k = -1 → v = -1 := by
        intro v hv
        rcases Int.units_eq_one_or v with h1 | h1
        · rw [h1, one_zpow] at hv
          exact absurd hv.symm hne
        · exact h1
      have hg2 : g.2 = 1 := by
        have hd : (orderOf g.2 : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hk3
        have hd2 : orderOf g.2 ∣ 2 ^ e := by
          have h0 : orderOf g.2 ∣ Nat.card (HGrp e) := by
            first
              | exact orderOf_dvd_natCard _
              | exact orderOf_dvd_card
          rwa [card_H] at h0
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
        have hi0 : i = 0 := by
          by_contra hne0
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          rw [hi, pow_succ] at hd
          push_cast at hd
          have h2k : (2 : ℤ) ∣ k := dvd_trans (Dvd.intro_left _ rfl) hd
          exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)
        rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
        exact hi
      exact Prod.ext (Prod.ext (hu _ hk1) (hu _ hk2)) hg2
    · rintro rfl
      exact Subgroup.mem_zpowers _
end Formalism.FrobeniusOrbits
