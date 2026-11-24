-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.twoAdicOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:11.995573+00:00
-- url     : https://prove2.me/submissions/8bf41978-3bf7-4607-8dd0-0fe5ab8f3817

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_pow_sub_one_ne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_val_even
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_powEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : TwoAdicOrder := by
  intro N a ha ha2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  split_ifs with h1
  · rw [h1, orderOf_one]
  · have hv : ∀ j : ℕ, 1 ≤ j →
        padicValInt 2 (a ^ 2 ^ j - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + j := by
      intro j hj
      have := val_even a ha ha2 (2 ^ j) (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rwa [padicValNat.prime_pow] at this
    have hpow : ∀ j : ℕ,
        ((a : ZMod (2 ^ N)) ^ 2 ^ j = 1 ↔ N ≤ padicValInt 2 (a ^ 2 ^ j - 1)) := fun j =>
      powEq N (2 ^ j) a (pow_sub_one_ne a ha2 _ (by positivity))
    set K := max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1)) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    have hK2 : N + 1 - padicValInt 2 (a ^ 2 - 1) ≤ K := le_max_right _ _
    have hK3 : K = 1 ∨ K = N + 1 - padicValInt 2 (a ^ 2 - 1) := max_choice _ _
    clear_value K
    obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    apply orderOf_eq_prime_pow
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero, pow_one]; exact h1
      · rw [hpow]
        have := hv n h0
        omega
    · rw [hpow]
      have := hv (n + 1) (by omega)
      omega
end Formalism.TwoAdicCyclotomicDecomposition
