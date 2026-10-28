-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_first_up_clock_positive_probability_all_smaller_levels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:26:36.654681+00:00
-- url     : https://prove2.me/submissions/9f6771e1-7af3-41fd-8424-3db10784a416

import Theorems.Thm_AvramDividend_Classical_unbounded_first_up_clock_positive_probability_before_horizon
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Any smaller positive level inherits a positive-probability upcrossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, 0 < b → b ≤ a →
      0 < P {ω : Ω | twoSidedExitUpTime X b ω < (t : ℝ≥0∞)} := by
  obtain ⟨a, ha, hP⟩ :=
    unbounded_first_up_clock_positive_probability_before_horizon X q hq hnbv t ht
  refine ⟨a, ha, ?_⟩
  intro b hb hba
  have hsubset :
      {ω : Ω | twoSidedExitUpTime X a ω < (t : ℝ≥0∞)} ⊆
        {ω : Ω | twoSidedExitUpTime X b ω < (t : ℝ≥0∞)} := by
    intro ω hω
    exact lt_of_le_of_lt (twoSidedExitUpTime_mono_threshold X b a hba ω) hω
  exact lt_of_lt_of_le hP (measure_mono hsubset)
