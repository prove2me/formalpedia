-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:22:48.207484+00:00
-- url     : https://prove2.me/submissions/071d8190-40cf-4c81-add8-13f3286b50cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- With finite terminal quadratic energy, capping the original ruin clock
cannot increase the Gaussian energy bracket of the source coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime) :
    ∀ ω, (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) ≤
      ∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime := by
  intro ω
  apply setIntegral_mono_set (hEnergy ω)
  · filter_upwards [] with t
    exact sq_nonneg (H (t, ω))
  · filter_upwards [] with t ht
    exact ⟨ht.1, ht.2.trans (min_le_right (τ ω) T)⟩
