-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.gcd_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:32.30783+00:00
-- url     : https://prove2.me/submissions/93e65144-5534-4a67-b4ab-6327ceae0b78

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral

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
theorem _root_.solution (N k : ℕ) (hk : k ≠ 0) : Nat.gcd (2 ^ N) k = 2 ^ min N (padicValNat 2 k) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv : padicValNat 2 (2 ^ v * m) = v := by
    rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [hv]
  have hcop : Nat.Coprime m (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]
  rcases le_total N v with h | h
  · rw [min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]
end Formalism.TwoAdicCyclotomicDecomposition
