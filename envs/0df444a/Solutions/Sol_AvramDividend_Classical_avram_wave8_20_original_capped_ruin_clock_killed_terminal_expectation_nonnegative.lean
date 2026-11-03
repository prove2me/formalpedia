-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:31:02.894102+00:00
-- url     : https://prove2.me/submissions/7331505b-e9d2-437f-915c-f2a3cbb0d257

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Capping at ruin does not introduce negative continuation expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    0 ≤ ∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  change 0 ≤ ∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P
  rw [avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
    X x D w q n]
  exact avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
    X x D w q (n : ℝ≥0)
