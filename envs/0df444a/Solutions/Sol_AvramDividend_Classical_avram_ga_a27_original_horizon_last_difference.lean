-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_original_horizon_last_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:19:42.436913+00:00
-- url     : https://prove2.me/submissions/b7cb9a0c-d923-493f-a1a4-cbc331577e38

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_horizon_clipped_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
open AvramDividend.Classical

/-- Identify the last stopped mesh cell with the original untruncated horizon increment. -/
theorem solution
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (n : ℝ≥0) (m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hρ : n ≤ ρ ω) :
    let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    (x + L (v (m + 1)) ω - D (v m) ω) -
      (x + L (v m) ω - D (v m) ω) =
        L n ω - L ((m : ℝ≥0) * Δ) ω := by
  intro Δ v
  have hEnd : v (m + 1) = n := by
    simpa only [v, Δ] using
      (avram_ga_a27_horizon_clipped_endpoint n m (ρ ω) hρ)
  have hPrev : v m = (m : ℝ≥0) * Δ := by
    change min ((m : ℝ≥0) * Δ) (ρ ω) = (m : ℝ≥0) * Δ
    exact min_eq_left (le_trans
      (avram_ga_a27_prehorizon_grid_le n m) hρ)
  rw [hEnd, hPrev]
  ring
