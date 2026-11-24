-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.order_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:26.489807+00:00
-- url     : https://prove2.me/submissions/494cb588-e633-48dc-ab82-97f4ada02933

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_card_H

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
theorem _root_.solution (e : ℕ) (x : HGrp e) (j : ℕ) : orderOf x ≤ 2 ^ j ↔ x ^ (2 ^ j) = 1 := by
  have hd : orderOf x ∣ 2 ^ e := by
    have h0 : orderOf x ∣ Nat.card (HGrp e) := by
      first
        | exact orderOf_dvd_natCard x
        | exact orderOf_dvd_card
    rwa [card_H] at h0
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rw [hi] at h
    have hij : i ≤ j := by
      by_contra hc
      push_neg at hc
      have hlt : 2 ^ j < 2 ^ i := by
        first
          | exact Nat.pow_lt_pow_right (by norm_num) hc
          | exact pow_lt_pow_right₀ (by norm_num) hc
          | exact Nat.pow_lt_pow_of_lt (by norm_num) hc
      exact absurd h (not_le.mpr hlt)
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hij
  · intro h
    exact Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h)
end Formalism.FrobeniusOrbits.Group
