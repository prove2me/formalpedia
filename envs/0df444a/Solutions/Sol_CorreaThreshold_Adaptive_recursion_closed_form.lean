-- Prove2me | solution 1 for CorreaThreshold.Adaptive.recursion_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:08:35.339275+00:00
-- url     : https://prove2.me/submissions/8c9134da-49a5-4322-94b5-c63c8e53f427

import Mathlib
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 2 ≤ n) (x : ℕ → ℝ) (hx0 : x 0 = 1)
    (j : ℕ) (hj : 1 ≤ j)
    (h8 : ∀ i ∈ Finset.Icc 1 j,
        x (i - 1) ^ n / n - x i ^ n / n =
          x i ^ (n - 1) / ((n : ℝ) - 1) - x (i + 1) ^ (n - 1) / ((n : ℝ) - 1)) :
    x (j + 1) ^ (n - 1) = ((n : ℝ) - 1) / n * x j ^ n + x 1 ^ (n - 1) - ((n : ℝ) - 1) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have key : ∀ k, k ≤ j → x (k + 1) ^ (n - 1) =
      ((n : ℝ) - 1) / n * x k ^ n + x 1 ^ (n - 1) - ((n : ℝ) - 1) / n := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hx0]; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have h := h8 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, hk⟩)
      simp only [Nat.add_sub_cancel] at h
      have h9 : x (k + 1 + 1) ^ (n - 1) = x (k + 1) ^ (n - 1) -
          ((n : ℝ) - 1) * (x k ^ n / n - x (k + 1) ^ n / n) := by
        rw [h]
        field_simp
        ring
      rw [h9, ih']
      field_simp
      ring
  exact key j le_rfl
