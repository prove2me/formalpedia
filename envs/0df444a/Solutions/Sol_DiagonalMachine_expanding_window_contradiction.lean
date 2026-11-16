-- Prove2me | solution 1 for DiagonalMachine.expanding_window_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:43.346198+00:00
-- url     : https://prove2.me/submissions/73ea2a3a-a892-473b-9d53-46002542eee1

import Mathlib
open MeasureTheory Set

theorem solution (H : Prop) (U : ℕ → ℝ → ℝ)
    (levels : ℕ → ℕ)
    (hcertificate : ∀ (j : ℕ) (y : ℝ), |y| ≤ (j:ℝ) → -1 ≤ U (levels j) y)
    (hentry : ¬H → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∃ y, |y| ≤ (j:ℝ) ∧ U (levels j) y < -1) : H := by
  by_contra hn
  obtain ⟨J, hJ⟩ := hentry hn
  obtain ⟨y, hy, hneg⟩ := hJ J le_rfl
  exact (not_lt_of_ge (hcertificate J y hy)) hneg
