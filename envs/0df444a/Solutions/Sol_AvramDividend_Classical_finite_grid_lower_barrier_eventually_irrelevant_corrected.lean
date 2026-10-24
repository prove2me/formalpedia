-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_lower_barrier_eventually_irrelevant_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:11:23.266142+00:00
-- url     : https://prove2.me/submissions/0ce52bef-7783-4d9a-8e5e-1ca4116075b7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (f : ℕ → ℝ) (z : ℝ) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ m →
      ((z < f k ∨ f k < -(n : ℝ)) ↔ z < f k) := by
  induction m with
  | zero =>
      obtain ⟨N, hN⟩ := exists_nat_gt (-f 0)
      refine ⟨N, ?_⟩
      intro n hn k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      constructor
      · intro h
        rcases h with h | h
        · exact h
        · have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          exfalso
          linarith
      · intro h
        exact Or.inl h
  | succ m ih =>
      obtain ⟨N₀, hN₀⟩ := ih
      obtain ⟨N₁, hN₁⟩ := exists_nat_gt (-f (m + 1))
      refine ⟨max N₀ N₁, ?_⟩
      intro n hn k hk
      by_cases hkm : k ≤ m
      · exact hN₀ n (le_trans (le_max_left N₀ N₁) hn) k hkm
      · have hkeq : k = m + 1 := by omega
        subst k
        constructor
        · intro h
          rcases h with h | h
          · exact h
          · have hlow : N₁ ≤ n :=
              le_trans (le_max_right N₀ N₁) hn
            have hcast : (N₁ : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast hlow
            exfalso
            linarith
        · intro h
          exact Or.inl h
