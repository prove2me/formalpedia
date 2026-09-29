-- Prove2me | solution 1 for EulerMascheroni.P2.factorial_binomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:45:02.188719+00:00
-- url     : https://prove2.me/submissions/b4494db4-b213-4e91-96f8-bba1a161e3eb

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.Tactic

open scoped BigOperators
open EulerMascheroni.P2

namespace FactorialBridge

lemma term (n k : ℕ) (hk : k ≤ n) :
    (n.factorial : ℚ) * coefficient n k =
      ((n-k).factorial : ℚ) * (n.choose (n-k) : ℚ)^3 *
        ((2*n-(n-k)).choose n : ℚ)^2 := by
  have hnk : 2*n-(n-k) = n+k := by omega
  rw [hnk, Nat.choose_symm hk, Nat.choose_symm_add]
  have hfac : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n-k).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  unfold coefficient
  rw [← hfac]
  have hkf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

end FactorialBridge

theorem solution (n : ℕ) : (n.factorial : ℚ) * Q n =
    ((∑ j ∈ Finset.range (n+1),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2 : ℕ) : ℚ) := by
  unfold Q
  rw [Finset.mul_sum]
  push_cast
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        ((n-k).factorial : ℚ) * (n.choose (n-k) : ℚ)^3 *
        ((2*n-(n-k)).choose n : ℚ)^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact FactorialBridge.term n k (by simpa using Finset.mem_range.mp hk)
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect
        (fun j => (j.factorial : ℚ) * (n.choose j : ℚ)^3 *
          ((2*n-j).choose n : ℚ)^2) (n+1)


