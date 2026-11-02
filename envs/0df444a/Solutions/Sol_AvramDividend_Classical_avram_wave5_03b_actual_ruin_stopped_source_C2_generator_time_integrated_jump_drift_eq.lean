-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:49:22.180732+00:00
-- url     : https://prove2.me/submissions/dc668042-5821-4a11-bdb4-59e7b87ab001

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped source Taylor compensator integrand agrees with the
Levy generator jump integrand after arbitrary time integration. This is a
drift identity, not a claim of martingale compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (μ : Measure ℝ≥0)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let S : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
    (∫ r in Ioc s t, (∫ z in B, S r *
      ((if Y r ∈ Icc (u + δ) v then
        w (Y r + z) - w (Y r) else 0) -
       (if -1 < z then
        z * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
        else 0)) ∂X.ν) ∂μ) =
    (∫ r in Ioc s t, (∫ z in B, S r *
      (if Y r ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) z else 0)
      ∂X.ν) ∂μ) := by
  let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
    (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
  let S : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
  change (∫ r in Ioc s t, (∫ z in B, S r *
      ((if Y r ∈ Icc (u + δ) v then
        w (Y r + z) - w (Y r) else 0) -
       (if -1 < z then
        z * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
        else 0)) ∂X.ν) ∂μ) =
    (∫ r in Ioc s t, (∫ z in B, S r *
      (if Y r ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) z else 0)
      ∂X.ν) ∂μ)
  apply integral_congr_ae
  filter_upwards [] with r
  simpa only [Y, S] using
    (avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
      X x D hD w u v δ (r, ω) B hBm hBneg)
