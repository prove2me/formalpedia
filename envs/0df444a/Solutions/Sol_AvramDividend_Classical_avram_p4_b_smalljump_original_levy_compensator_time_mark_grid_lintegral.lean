-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_levy_compensator_time_mark_grid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:02.751212+00:00
-- url     : https://prove2.me/submissions/7df01a42-73bb-405a-bbb2-a520d9bec205

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The nonnegative predictable-simple compensator of the original Levy
jump measure integrates cell by cell against physical time and X.nu. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) :
    (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
      (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p
      ∂(timeMeasure.prod X.ν)) =
    ∑ i ∈ S, c i *
      (timeMeasure.prod X.ν)
        (Ioc (s i) (t i) ×ˢ B i) := by
  have hm (i : ι) (hi : i ∈ S) : Measurable
      (fun p : ℝ≥0 × ℝ =>
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p) :=
    measurable_const.indicator (measurableSet_Ioc.prod (hB i hi))
  rw [lintegral_finset_sum S hm]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const
    (measurableSet_Ioc.prod (hB i hi)) (c i)
