-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.twistVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:27.440881+00:00
-- url     : https://prove2.me/submissions/25c0cc85-29b8-4f2a-80d3-e2bbee828016

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_v24
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_v4
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twoAdicVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : TwistVal := by
  intro s e he
  have h5 : Odd (5 : ℤ) := by decide
  have h52 : (5 : ℤ) ^ 2 ≠ 1 := by norm_num
  have hpos : 0 < 2 ^ s * e := Nat.mul_pos (Nat.two_pow_pos s) he
  have key := (twoAdicVal 5 h5 h52 (2 ^ s * e) hpos).1
  rw [key]
  split_ifs with hev
  · rw [v24, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
    omega
  · rw [v4]
    have hs : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · exfalso; apply hev
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
        exact ⟨2 ^ k * e, by ring⟩
    subst hs
    have he' : ¬ 2 ∣ e := by
      intro hd; apply hev; simpa using (even_iff_two_dvd.mpr hd)
    rw [padicValNat.eq_zero_of_not_dvd he']
end Formalism.TwoAdicCyclotomicDecomposition
