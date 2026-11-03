-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:53:42.084981+00:00
-- url     : https://prove2.me/submissions/f98d7544-7c6c-4720-9cba-44b0e43763f9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source capped-ruin killed continuation expectation agrees at finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P) =
    (∫ ω, (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
      else 0) ∂P) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  change (∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P) =
    (∫ ω, (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
      else 0) ∂P)
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω =>
    avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
      X x D w q ω n)
