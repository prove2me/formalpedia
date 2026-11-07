-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_BV_source_mass_integrable_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:13:01.996376+00:00
-- url     : https://prove2.me/submissions/268d82d9-5e5f-44f9-a807-a6e13e7cc43b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_X_integrable_any_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) P ∧
    (∀ ω, 0 ≤
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · have hR : Integrable (fun ω =>
        (T : ℝ) * X.drift - X.X T ω) P :=
      (integrable_const _).sub
        (avram_p3_comp8_original_X_integrable_any_clock X hX hBV T)
    exact (integrable_const _).add hR.abs
  · intro ω
    positivity
