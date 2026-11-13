-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a28_compact_modulus_last_increment
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T14:43:38.971116+00:00
-- url     : https://prove2.me/submissions/044857f6-90a5-4e7a-ab73-db90f463e410

import Mathlib

open Filter

set_option autoImplicit false

/-- If `z - y → 0` and both sequences are eventually in a compact interval where `w` has the
uniform modulus `hmod`, then `w (z m) - w (y m) → 0`. -/
theorem solution (w : ℝ → ℝ) (a b : ℝ) (y z : ℕ → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, u ∈ Set.Icc a b → v ∈ Set.Icc a b →
        |v - u| < δ → |w v - w u| < ε)
    (hy : ∀ᶠ m in atTop, y m ∈ Set.Icc a b)
    (hz : ∀ᶠ m in atTop, z m ∈ Set.Icc a b)
    (hd : Tendsto (fun m => z m - y m) atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (z m) - w (y m)) atTop (nhds (0 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases hmod ε hε with ⟨δ, hδpos, hδ⟩
  rw [Metric.tendsto_atTop] at hd
  rcases hd δ hδpos with ⟨N₀, hN₀⟩
  rw [Filter.eventually_atTop] at hy hz
  rcases hy with ⟨N₁, hN₁⟩
  rcases hz with ⟨N₂, hN₂⟩
  refine ⟨max N₀ (max N₁ N₂), ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  rw [Real.dist_eq, sub_zero]
  exact hδ (y n) (z n) (hN₁ n hn₁) (hN₂ n hn₂)
    (by simpa [Real.dist_eq, sub_zero] using hN₀ n hn₀)
