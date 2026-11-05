-- Prove2me | solution 1 for CircuitLowerBound.lin_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:26:46.840726+00:00
-- url     : https://prove2.me/submissions/b6499e3e-a9a3-422b-83a7-dc6128722827

import Mathlib.Tactic

set_option autoImplicit false
section
section

theorem solution : ∀ x : ℕ, 8 ≤ x → 24 * x + 26 ≤ 2 ^ x := by
  intro x hx
  induction x with
  | zero => omega
  | succ n ih =>
    rw [pow_succ]
    by_cases hn : 8 ≤ n
    · have h := ih hn
      omega
    · have hn' : n = 7 := by omega
      subst n
      norm_num
