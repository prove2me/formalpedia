-- Prove2me | solution 1 for AvramDividend.Classical.survival_event_measurable_of_stopping_and_admissible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:28:40.540767+00:00
-- url     : https://prove2.me/submissions/fc4b74a8-9e8f-4568-8289-aadd1dcd6972

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    MeasurableSet {ω : Ω | τ ω < ruinTime X x D ω} := by
  have h1 : Measurable τ := hτ.measurable'
  exact measurableSet_lt h1 (AvramDividend.Classical.ruinTime_measurable X x D hD)
