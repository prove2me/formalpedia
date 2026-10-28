-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_test_aestronglyMeasurable_of_progressive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:28:48.28627+00:00
-- url     : https://prove2.me/submissions/7e47a40a-8651-45c6-bda5-5923791f8fdf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : Measurable w)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (hτ : IsStoppingTime 𝓕 τ)
    (hSurvive : MeasurableSet
      {ω : Ω | τ ω < ruinTime X x D ω}) :
    AEStronglyMeasurable
      (fun ω => if τ ω < ruinTime X x D ω then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) P := by
  have h1 : Measurable (stoppedValue (riskProcess X x D) τ) :=
    (measurable_stoppedValue hProg hτ).mono hτ.measurableSpace_le le_rfl
  exact (Measurable.ite hSurvive (hw.comp h1) measurable_const).aestronglyMeasurable
