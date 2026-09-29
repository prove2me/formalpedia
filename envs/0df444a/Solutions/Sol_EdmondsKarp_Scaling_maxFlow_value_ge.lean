-- Prove2me | solution 1 for EdmondsKarp.Scaling.maxFlow_value_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:17.674278+00:00
-- url     : https://prove2.me/submissions/fbdeba97-3452-4cae-b495-6a3bb0411a20

import Mathlib

theorem solution {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (hsum : ∑ i, a i = ∑ j, b j) (p : ℕ) :
    max 0 (((∑ i, a i : ℕ) : ℝ) / 2 ^ p - ((max m n : ℕ) : ℝ)) ≤
      ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by
  have hpow : (0:ℝ) < 2 ^ p := by positivity
  have hpow' : (0:ℕ) < 2 ^ p := Nat.two_pow_pos p
  -- each floor is within 1 of the exact quotient
  have hfloor : ∀ x : ℕ, ((x : ℝ)) / 2 ^ p ≤ ((x / 2 ^ p : ℕ) : ℝ) + 1 := by
    intro x
    rw [div_le_iff₀ hpow]
    have h1 : 2 ^ p * (x / 2 ^ p) + x % 2 ^ p = x := Nat.div_add_mod x (2 ^ p)
    have h2 : x % 2 ^ p < 2 ^ p := Nat.mod_lt x hpow'
    have h3 : (x : ℝ) = 2 ^ p * ((x / 2 ^ p : ℕ) : ℝ) + ((x % 2 ^ p : ℕ) : ℝ) := by
      exact_mod_cast h1.symm
    have h4 : ((x % 2 ^ p : ℕ) : ℝ) < ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h4
    rw [h3]
    nlinarith
  have key : ∀ (r : ℕ) (f : Fin r → ℕ),
      ((∑ i, f i : ℕ) : ℝ) / 2 ^ p - (r : ℝ) ≤ ((∑ i, f i / 2 ^ p : ℕ) : ℝ) := by
    intro r f
    have h1 : ((∑ i, f i : ℕ) : ℝ) / 2 ^ p = ∑ i, ((f i : ℝ) / 2 ^ p) := by
      push_cast
      rw [Finset.sum_div]
    have h2 : ∑ i, ((f i : ℝ) / 2 ^ p) ≤ ∑ i : Fin r, (((f i / 2 ^ p : ℕ) : ℝ) + 1) :=
      Finset.sum_le_sum fun i _ => hfloor (f i)
    have h3 : ∑ i : Fin r, (((f i / 2 ^ p : ℕ) : ℝ) + 1)
        = ((∑ i, f i / 2 ^ p : ℕ) : ℝ) + (r : ℝ) := by
      rw [Finset.sum_add_distrib]
      push_cast
      simp
    rw [h1]
    linarith [h2, h3.le, h3.ge]
  have ha := key m a
  have hb := key n b
  have hmn : (m : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
    exact_mod_cast le_max_left m n
  have hnm : (n : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
    exact_mod_cast le_max_right m n
  have hsumR : ((∑ i, a i : ℕ) : ℝ) = ((∑ j, b j : ℕ) : ℝ) := by exact_mod_cast hsum
  refine max_le (by positivity) ?_
  rcases le_total (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) with hcase | hcase
  · rw [Nat.min_eq_left hcase]
    linarith
  · rw [Nat.min_eq_right hcase]
    rw [hsumR] at *
    linarith
