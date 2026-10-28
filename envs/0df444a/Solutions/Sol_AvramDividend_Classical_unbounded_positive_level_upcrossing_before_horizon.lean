-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_level_upcrossing_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:18:37.55154+00:00
-- url     : https://prove2.me/submissions/e8e22954-b585-4d2b-afab-2191e9c91c3f

import Theorems.Thm_AvramDividend_Classical_unbounded_levy_positive_upward_increment_measure_all_times
import Theorems.Thm_AvramDividend_Classical_positive_measure_positive_real_tail_contains_positive_level
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before every positive horizon there is a strictly positive level
that the unbounded-variation process crosses with positive probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧
      0 < P {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ a < X.X s ω} := by
  have htpos :
      0 < P {ω : Ω | 0 < X.X t ω} :=
    unbounded_levy_positive_upward_increment_measure_all_times
      X q hq hnbv t ht
  obtain ⟨a, ha, hmeasure⟩ :=
    positive_measure_positive_real_tail_contains_positive_level
      P (fun ω : Ω => X.X t ω) htpos
  refine ⟨a, ha, ?_⟩
  have hsub :
      {ω : Ω | a < X.X t ω} ⊆
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ a < X.X s ω} := by
    intro ω hω
    exact ⟨t, le_rfl, hω⟩
  exact lt_of_lt_of_le hmeasure (measure_mono hsub)
