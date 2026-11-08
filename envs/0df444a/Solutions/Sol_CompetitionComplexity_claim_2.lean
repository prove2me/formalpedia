-- Prove2me | solution 1 for CompetitionComplexity.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:23:04.311879+00:00
-- url     : https://prove2.me/submissions/ad6575d9-9723-430e-95e4-6e2e7d9032e6

import Mathlib

theorem solution (n : ℕ) (hn : 1 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ ((n : ℝ) / ((n : ℝ) - 1)) ^ (1 / (n : ℝ)) * x ^ (((n : ℝ) - 1) / (n : ℝ)) := by
  obtain ⟨h0, h1⟩ := hx
  have hn' : (1:ℝ) < n := by exact_mod_cast hn
  have hc : 1 ≤ (n:ℝ) / ((n:ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hA : 1 ≤ ((n:ℝ) / ((n:ℝ) - 1)) ^ (1 / (n:ℝ)) :=
    Real.one_le_rpow hc (by positivity)
  have hB : x ≤ x ^ (((n:ℝ) - 1) / (n:ℝ)) := by
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; exact Real.rpow_nonneg le_rfl _
    · calc x = x ^ (1:ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (((n:ℝ) - 1) / (n:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge h h1 (by rw [div_le_one (by linarith)]; linarith)
  have hBn : 0 ≤ x ^ (((n:ℝ) - 1) / (n:ℝ)) := Real.rpow_nonneg h0 _
  nlinarith
