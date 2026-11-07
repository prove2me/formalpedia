-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_BV_source_variation_L1_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:35:05.654975+00:00
-- url     : https://prove2.me/submissions/b9b73dae-f1fe-4e8b-a4a5-ed57e9168c9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual BV drift and source-jump variation have a finite first-moment
envelope on every physical horizon up to one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1) :
    Integrable (fun ω =>
      |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|) P ∧
    (∀ ω, 0 ≤
      |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|) := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · exact (integrable_const _).add
      ((avram_wave5_04c_actual_bv_residual_integrable_upto_one
        X hX hBV T hT).abs)
  · intro ω
    positivity
