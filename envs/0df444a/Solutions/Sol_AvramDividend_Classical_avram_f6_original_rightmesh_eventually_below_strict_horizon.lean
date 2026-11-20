-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_rightmesh_eventually_below_strict_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:07:21.028888+00:00
-- url     : https://prove2.me/submissions/ca1baa0a-b5e4-4a5d-8e53-90e4402ad543

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (σ τ : ℝ≥0) (hστ : σ < τ) :
    ∀ᶠ m : ℕ in atTop,
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) < τ := by
  have hreal : (σ : ℝ) < (τ : ℝ) := by exact_mod_cast hστ
  have hclock := avram_f6_original_delayed_clock_real_min_tends_to_stopped
    σ τ (le_of_lt hστ)
  have hev : ∀ᶠ m : ℕ in atTop,
      min (τ : ℝ) ((σ : ℝ) + (1 : ℝ) / ((m : ℝ) + 1)) <
        (τ : ℝ) := hclock.eventually (eventually_lt_nhds hreal)
  filter_upwards [hev] with m hm
  exact_mod_cast hm
