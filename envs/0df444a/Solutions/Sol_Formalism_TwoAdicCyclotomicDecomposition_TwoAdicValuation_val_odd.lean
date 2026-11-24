-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:08.504805+00:00
-- url     : https://prove2.me/submissions/1e267d51-1cc1-4611-b7ae-5e7b7fb8435a

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_geom_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
theorem _root_.solution (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (hod : Odd e) :
    padicValInt 2 (a ^ e - 1) = padicValInt 2 (a - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have hs : Odd (∑ i ∈ Finset.range e, a ^ i) := (geom_odd a ha e).mpr hod
  have hs0 : (∑ i ∈ Finset.range e, a ^ i) ≠ 0 := fun h => by
    rw [h] at hs; exact Int.not_even_iff_odd.mpr hs ⟨0, by norm_num⟩
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, a ^ i := by
    intro hd
    exact Int.not_even_iff_odd.mpr hs (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  rw [← mul_geom_sum, padicValInt.mul h1 hs0, padicValInt.eq_zero_of_not_dvd hnd, add_zero]
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
