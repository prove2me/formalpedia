-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_upper_ae_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:01:56.59201+00:00
-- url     : https://prove2.me/submissions/6e10b742-eae1-48f2-b068-46f33cc9ffcd

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The same full-measure path set obeys the BV drift upper bound along any countable schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (ts : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      X.X (ts n) ω ≤ ((ts n : ℝ≥0) : ℝ) * X.drift := by
  exact ae_all_iff.mpr (fun n =>
    bv_actual_levy_drift_upper_ae_fixed_time X hBV (ts n))
