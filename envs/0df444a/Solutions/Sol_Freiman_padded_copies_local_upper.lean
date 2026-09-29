-- Prove2me | solution 1 for Freiman.padded_copies_local_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:13.763258+00:00
-- url     : https://prove2.me/submissions/a575bf38-9a01-4ee7-808b-7b9c2e2d1726

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Theorems.Thm_Freiman_padded_copies_window_cases
import Theorems.Thm_Freiman_localValue_window_comparison
import Theorems.Thm_Freiman_localValue_constant
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t)
    (R J : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hJ : ∀ j : ℕ, J ≤ j → ε j ≤ δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → localValue b (n : ℤ) ≤ t + δ + 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := padded_copies_window_cases a b d hcopy hpad R J
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨j, hj, i, hw⟩ | hw
  · have he := (abs_le.mp (localValue_window_comparison b (a j) (n : ℤ) i R hw)).2
    linarith [hbound j i, hJ j hj]
  · have he := (abs_le.mp (localValue_window_comparison b (fun _ : ℤ => d) (n : ℤ) 0 R hw)).2
    rw [localValue_constant] at he
    linarith
