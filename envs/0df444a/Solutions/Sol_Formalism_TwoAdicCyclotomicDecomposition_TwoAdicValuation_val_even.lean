-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.val_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:17.629344+00:00
-- url     : https://prove2.me/submissions/cb1ff647-bd2b-4696-b5e8-a0c0531ebd82

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_vEq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_vNat
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_pow_sub_one_ne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_sq_split

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
theorem _root_.solution (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) (hev : Even e) :
    padicValInt 2 (a ^ e - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne := pow_sub_one_ne a ha2 e he
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  have hdiv : (2 : ℤ) ∣ a - 1 := by
    obtain ⟨k, rfl⟩ := ha; exact ⟨k, by ring⟩
  have hnd : ¬ (2 : ℤ) ∣ a := by
    rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ha
  have key := Int.two_pow_sub_pow (y := 1) (n := e) hdiv hnd hev
  rw [one_pow, ← vEq _ hne, ← vEq _ h2, ← vEq _ h1, ← vNat _ he.ne'] at key
  rw [sq_split a ha2]
  norm_cast at key
  omega
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
