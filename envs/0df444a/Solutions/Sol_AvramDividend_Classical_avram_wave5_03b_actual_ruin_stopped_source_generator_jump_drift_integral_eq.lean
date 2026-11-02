-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:05:16.3554+00:00
-- url     : https://prove2.me/submissions/42b1cc94-776e-4cf3-bc78-ee1229cb629a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact stopped original-source Taylor drift integrates as the genuine
source Lévy jump generator over every measurable negative mark band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (p : ℝ≥0 × Ω) (B : Set ℝ)
    (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    let S : ℝ :=
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    (∫ z in B, S *
      ((if Y p ∈ Icc (u + δ) v then
         w (Y p + z) - w (Y p) else 0) -
       (if -1 < z then
         z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
         else 0)) ∂X.ν) =
    ∫ z in B, S *
      (if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0)
      ∂X.ν := by
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
  let S : ℝ :=
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  change
    (∫ z in B, S *
      ((if Y p ∈ Icc (u + δ) v then
         w (Y p + z) - w (Y p) else 0) -
       (if -1 < z then
         z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
         else 0)) ∂X.ν) =
    ∫ z in B, S *
      (if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0)
      ∂X.ν
  have hkernel (z : ℝ) (hz : z < 0) :
      ((if Y p ∈ Icc (u + δ) v then
          w (Y p + z) - w (Y p) else 0) -
       (if -1 < z then
          z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
          else 0)) =
      (if Y p ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0) :=
    avram_wave5_03b_actual_source_taylor_generator_kernel_eq
      X x D hD w u v δ p z hz
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hBm] with z hz
  exact congrArg (fun h : ℝ => S * h) (hkernel z (hBneg hz))
