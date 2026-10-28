-- Prove2me | solution 1 for AvramDividend.Classical.downward_grid_limsup_of_eventual_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:37:35.691918+00:00
-- url     : https://prove2.me/submissions/46cdc119-2e81-403f-a3ac-c2f5ac200a10

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open scoped NNReal

theorem solution
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (f : ℝ≥0 → ℝ) (g : ℕ → ℝ≥0 → ℝ) (a ε : ℝ)
    (hclose : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℝ≥0, |f t - g n t| ≤ ε)
    (happroxdrops : ∀ N : ℕ, ∃ n ≥ N, ∃ ij ∈ grid n,
      g n ij.2 - g n ij.1 < -(a + 2 * ε)) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ ij ∈ grid n,
      f ij.2 - f ij.1 < -a := by
  obtain ⟨N₀, hbound⟩ := hclose
  intro N
  obtain ⟨n, hn, ij, hij, hdrop⟩ := happroxdrops (max N N₀)
  refine ⟨n, (le_max_left N N₀).trans hn, ij, hij, ?_⟩
  have h1 := (abs_le.mp (hbound n ((le_max_right N N₀).trans hn) ij.2)).2
  have h2 := (abs_le.mp (hbound n ((le_max_right N N₀).trans hn) ij.1)).1
  linarith