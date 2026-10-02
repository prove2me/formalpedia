-- Prove2me | solution 1 for CookPvsNP.comp_budget
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:12:17.276401+00:00
-- url     : https://prove2.me/submissions/60abd08f-9428-4959-ac11-1b01b1bd913d

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

private theorem absorb (A d B : ℕ) : ∃ k, ∀ n : ℕ, A * (n + 1) ^ d + B ≤ n ^ k + k := by
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
    A * (n + 1) ^ d + B ≤ n ^ A * (n ^ 2) ^ d + B := by
      gcongr
    _ = n ^ (A + 2 * d) + B := by rw [pow_add, pow_mul]
    _ ≤ n ^ k + k := Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) (by dsimp [k]; omega)) (by dsimp [k]; omega)

/-- All linear simulation overhead and the nested source budgets fit one Cook exponent. -/
theorem solution (k₁ k₂ : ℕ) : ∃ k, ∀ n : ℕ,
    20 * (n + (n ^ k₁ + k₁) + ((n + (n ^ k₁ + k₁) + 1) ^ k₂ + k₂) + 1) ≤
      n ^ k + k := by
  let a := k₁ + 3
  let d := (k₁ + 1) * (k₂ + 1)
  obtain ⟨k, hk⟩ := absorb (20 * (a + a ^ k₂)) d (20 * k₂)
  refine ⟨k, fun n => le_trans ?_ (hk n)⟩
  have hn : 0 < n + 1 := by omega
  have hd : k₁ + 1 ≤ d := by dsimp [d]; nlinarith
  have hd₂ : (k₁ + 1) * k₂ ≤ d := by dsimp [d]; nlinarith
  have hpow : 1 ≤ (n + 1) ^ (k₁ + 1) := by
    have : 0 < (n + 1) ^ (k₁ + 1) := by positivity
    omega
  have hp₁ : n ≤ (n + 1) ^ (k₁ + 1) := by
    calc
      n ≤ n + 1 := by omega
      _ = (n + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hn (by omega)
  have hp₂ : n ^ k₁ ≤ (n + 1) ^ (k₁ + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k₁).trans (Nat.pow_le_pow_right hn (by omega))
  have hbase : n + (n ^ k₁ + k₁) + 1 ≤ a * (n + 1) ^ (k₁ + 1) := by
    dsimp [a]
    nlinarith
  have h₁ : n + (n ^ k₁ + k₁) + 1 ≤ a * (n + 1) ^ d :=
    hbase.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hn hd))
  have h₂ : (n + (n ^ k₁ + k₁) + 1) ^ k₂ ≤ a ^ k₂ * (n + 1) ^ d := by
    calc
      _ ≤ (a * (n + 1) ^ (k₁ + 1)) ^ k₂ := Nat.pow_le_pow_left hbase k₂
      _ = a ^ k₂ * (n + 1) ^ ((k₁ + 1) * k₂) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hd₂)
  nlinarith

#print axioms solution
