-- Prove2me | solution 1 for ChvatalOneHard398.SAT.theorem_26_bitRecovery
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:28.95879+00:00
-- url     : https://prove2.me/submissions/94aab73b-8c89-488d-90ed-437ab82a557b

import Mathlib

private theorem bitRecoveryInvariant (d : ℕ) (u : ℕ → ℕ)
    (h0 : u 0 = 0)
    (hstep : ∀ k, u (k+1) = if d % 2^(k+1) = u k then u k else u k + 2^k) :
    ∀ k, u k = d % 2^k := by
  intro k
  induction k with
  | zero => exact h0.trans (Nat.mod_one d).symm
  | succ k ih =>
      have hmod : d % 2^(k+1) % 2^k = d % 2^k := by
        rw [pow_succ]
        exact Nat.mod_mul_right_mod d (2^k) 2
      have hdiv : d % 2^(k+1) / 2^k = d / 2^k % 2 := by
        rw [pow_succ]
        exact Nat.mod_mul_right_div_self d (2^k) 2
      have hdecomp := Nat.mod_add_div (d % 2^(k+1)) (2^k)
      rw [hmod, hdiv] at hdecomp
      rcases Nat.mod_two_eq_zero_or_one (d / 2^k) with hq | hq
      · rw [hq, mul_zero, add_zero] at hdecomp
        rw [hstep, ih, ← hdecomp, if_pos rfl]
      · rw [hq, mul_one] at hdecomp
        have hne : d % 2^(k+1) ≠ d % 2^k := by
          rw [← hdecomp]
          have hp : 0 < 2^k := Nat.two_pow_pos k
          omega
        rw [hstep, ih, if_neg hne]
        exact hdecomp

theorem solution (d : ℕ) (u : ℕ → ℕ)
    (h0 : u 0 = 0)
    (hstep : ∀ k, u (k+1) = if d % 2^(k+1) = u k then u k else u k + 2^k) :
    (∀ k, u k = d % 2^k) ∧ ∀ K, d < 2^K → u K = d := by
  refine ⟨bitRecoveryInvariant d u h0 hstep, ?_⟩
  intro K hd
  rw [bitRecoveryInvariant d u h0 hstep K, Nat.mod_eq_of_lt hd]
