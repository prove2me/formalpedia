-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_terminal_spatial_eventually_zero_pre_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:38:15.843092+00:00
-- url     : https://prove2.me/submissions/c65d60cf-f750-43de-85fc-9bab4768916f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_nnreal_eventual_terminal_saturation
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_spatial_zero_after_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (x : ℝ)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0) (ω : Ω) (hρ : ρ ω < n) :
    ∀ᶠ m : ℕ in Filter.atTop,
      let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      w (x + L (v (m + 1)) ω - D (v m) ω) -
        w (x + L (v m) ω - D (v m) ω) = 0 := by
  obtain ⟨k, hk⟩ :=
    AvramDividend.Classical.avram_ga_a27_nnreal_eventual_terminal_saturation
      (ρ ω) n hρ
  filter_upwards [Filter.eventually_ge_atTop k] with m hm
  exact AvramDividend.Classical.avram_ga_a26_terminal_spatial_zero_after_stop
    L D w x n m ρ ω (hk m hm)
