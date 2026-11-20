-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_kappa_clock_equals_first_negative_mark_when_ruin_clipped_and_upper_exit_later
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:44:22.982201+00:00
-- url     : https://prove2.me/submissions/4ce723fc-b503-416e-bc7f-7268276714fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (ρ : Ω → ℝ≥0) (κ : ℕ → Ω → ℝ≥0)
    (k : ℕ) (σ : ℝ≥0)
    (hρ : ρ ω = σ)
    (hκ : κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hUpper : (σ : ℝ≥0∞) ≤
      twoSidedExitUpTime X ((k : ℝ) + 1) ω) :
    κ k ω = σ := by
  rw [hκ, hρ, min_eq_left hUpper]
  rfl
