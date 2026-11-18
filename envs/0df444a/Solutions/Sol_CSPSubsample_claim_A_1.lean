-- Prove2me | solution 1 for CSPSubsample.claim_A_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:08:49.317528+00:00
-- url     : https://prove2.me/submissions/d35904b9-b207-433a-9ecc-92b723823652

import Mathlib

set_option autoImplicit false
namespace CSPSubsample

theorem claim_A_1 (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    1 - (k : ℝ) ^ 2 / N ≤ (N.descFactorial k : ℝ) / (N : ℝ) ^ k ∧
      (N.descFactorial k : ℝ) / (N : ℝ) ^ k ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (0 : ℝ) < (N : ℝ) ^ k := pow_pos hN k
  have key : ∀ j : ℕ, j ≤ N →
      (N : ℝ) ^ j * ((N : ℝ) - (j : ℝ) ^ 2) ≤ (N : ℝ) * (N.descFactorial j : ℝ) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hjN : (j : ℝ) ≤ N := by exact_mod_cast (show j ≤ N by omega)
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
      have h1 : 0 ≤ (N : ℝ) - j := by linarith
      have h2 := mul_le_mul_of_nonneg_left ih' h1
      have h3 : (N : ℝ) ^ (j + 1) * ((N : ℝ) - ((j + 1 : ℕ) : ℝ) ^ 2)
          ≤ ((N : ℝ) - j) * ((N : ℝ) ^ j * ((N : ℝ) - (j : ℝ) ^ 2)) := by
        have hx : 0 ≤ (N : ℝ) ^ j := pow_nonneg hN.le j
        have : ((N : ℝ) - j) * ((N : ℝ) - (j : ℝ) ^ 2) - (N : ℝ) * ((N : ℝ) - ((j : ℝ) + 1) ^ 2)
            = (j : ℝ) * N + N + (j : ℝ) ^ 3 := by ring
        have hpos : 0 ≤ (j : ℝ) * N + N + (j : ℝ) ^ 3 := by positivity
        push_cast
        rw [pow_succ]
        nlinarith [mul_nonneg hx hpos]
      calc (N : ℝ) ^ (j + 1) * ((N : ℝ) - ((j + 1 : ℕ) : ℝ) ^ 2)
          ≤ ((N : ℝ) - j) * ((N : ℝ) ^ j * ((N : ℝ) - (j : ℝ) ^ 2)) := h3
        _ ≤ ((N : ℝ) - j) * ((N : ℝ) * (N.descFactorial j : ℝ)) := h2
        _ = (N : ℝ) * (((N : ℝ) - j) * (N.descFactorial j : ℝ)) := by ring
  constructor
  · have hk' := key k hkN
    rw [le_div_iff₀ hpow]
    have : (1 - (k : ℝ) ^ 2 / N) * (N : ℝ) ^ k * N = (N : ℝ) ^ k * ((N : ℝ) - (k : ℝ) ^ 2) := by
      field_simp
    nlinarith
  · rw [div_le_one hpow]
    exact_mod_cast Nat.descFactorial_le_pow N k

end CSPSubsample

theorem solution (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    1 - (k : ℝ) ^ 2 / N ≤ (N.descFactorial k : ℝ) / (N : ℝ) ^ k ∧
      (N.descFactorial k : ℝ) / (N : ℝ) ^ k ≤ 1 :=
  CSPSubsample.claim_A_1 k N hk hkN
