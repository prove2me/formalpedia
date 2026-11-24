-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.card_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:14:01.42382+00:00
-- url     : https://prove2.me/submissions/c1bc610a-5bbf-4dfc-bc96-a63ed6fe4381

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_cast_eq_neg_one

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
namespace Formalism.FrobeniusOrbits.Group
theorem _root_.solution (e : ℕ) : Nat.card (HGrp e) = 2 ^ e := by
  have hc : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega), show e + 2 - 1 = e + 1 by omega]
    simp
  have ho : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 := by
    apply orderOf_eq_prime
    · exact neg_one_sq
    · intro h
      have h' : ((1 : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
        have h0 := congrArg Units.val h
        simp only [Units.val_neg, Units.val_one] at h0
        rw [Int.cast_one]
        exact h0.symm
      rw [cast_eq_neg_one] at h'
      have h5 := Int.le_of_dvd (by norm_num) h'
      push_cast at h5
      have h2 : (2 : ℤ) ^ (e + 2) = 4 * 2 ^ e := by ring
      have h3 : (0 : ℤ) < 2 ^ e := by positivity
      rw [h2] at h5
      generalize (2 : ℤ) ^ e = s at h3 h5
      omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ho, hc] at h
  unfold HGrp
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h.symm.trans (pow_succ 2 e))
end Formalism.FrobeniusOrbits.Group
