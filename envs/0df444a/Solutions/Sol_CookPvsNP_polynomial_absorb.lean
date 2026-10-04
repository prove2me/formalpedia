-- Prove2me | solution 1 for CookPvsNP.polynomial_absorb
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:28:08.495978+00:00
-- url     : https://prove2.me/submissions/c2e1c7c8-baae-4cff-bab6-7e1f337912b1

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

theorem solution (A d B : ℕ) : ∃ k, ∀ n : ℕ, A * (n + 1) ^ d + B ≤ n ^ k + k := by
  let k := A + 2 * d + A * 2 ^ d + B + 1
  refine ⟨k, ?_⟩
  intro n
  by_cases hz : n = 0
  · subst n
    simp only [Nat.zero_add, one_pow, Nat.mul_one]
    dsimp [k]
    omega
  by_cases ho : n = 1
  · subst n
    simp only [one_pow]
    dsimp [k]
    omega
  have hn : 2 ≤ n := by omega
  have hc : A ≤ n ^ A :=
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))).trans (Nat.pow_le_pow_left hn A)
  have hb : n + 1 ≤ n ^ 2 := by nlinarith
  calc
    A * (n + 1) ^ d + B ≤ n ^ A * (n ^ 2) ^ d + B := by gcongr
    _ = n ^ (A + 2 * d) + B := by rw [pow_add, pow_mul]
    _ ≤ n ^ k + k := Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)) (by dsimp [k]; omega)

#print axioms solution
