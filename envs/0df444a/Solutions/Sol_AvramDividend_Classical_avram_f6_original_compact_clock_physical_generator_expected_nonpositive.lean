-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_compact_clock_physical_generator_expected_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:55:43.109299+00:00
-- url     : https://prove2.me/submissions/8d2ecd98-ceef-4831-844e-e68bbac221b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_physical_generator_drift_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (k : ℕ) (μ : Measure ℝ≥0)
    (hGInt : ∀ ω : Ω, Integrable
      (fun t : ℝ≥0 =>
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0) μ)
    (hGI : Integrable (fun ω : Ω => (∫ t : ℝ≥0,
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0 ∂μ)) P) :
    (∫ ω : Ω, (∫ t : ℝ≥0,
        let Y : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < Y ∧ ENNReal.ofReal Y < C ∧ t ≤ σ k ω then
          Real.exp (-(q * (t : ℝ))) *
            (X.generator w Y - q * w Y)
        else 0 ∂μ) ∂P) ≤ 0 := by
  have hpath := avram_f6_original_compact_clock_physical_generator_drift_nonpositive
    X x q w C hw_gen D σ k μ hGInt
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall hpath
