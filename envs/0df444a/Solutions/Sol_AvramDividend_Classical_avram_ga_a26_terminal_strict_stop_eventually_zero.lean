-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_terminal_strict_stop_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:36:04.873318+00:00
-- url     : https://prove2.me/submissions/5eaeca89-eb5c-4441-b497-104d6d7f227e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_grid_eventually_beyond_strict_stop
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_spatial_zero_after_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (x : ℝ) (n : ℝ≥0) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hr : ρ ω < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      w (x + L (v (m + 1)) ω - D (v m) ω) -
        w (x + L (v m) ω - D (v m) ω) = 0 := by
  have hrR : (ρ ω : ℝ) < (n : ℝ) := by exact_mod_cast hr
  obtain ⟨k, hk⟩ := avram_ga_a26_grid_eventually_beyond_strict_stop
    (n : ℝ) (ρ ω : ℝ) (by positivity) hrR
  refine ⟨k, ?_⟩
  intro m hm
  have hgridR := hk m hm
  have hgrid : ρ ω ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) := by
    exact_mod_cast hgridR
  exact avram_ga_a26_terminal_spatial_zero_after_stop L D w x n m ρ ω hgrid
