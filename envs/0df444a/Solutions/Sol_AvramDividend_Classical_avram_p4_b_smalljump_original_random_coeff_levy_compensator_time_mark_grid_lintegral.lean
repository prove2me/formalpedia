-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:08.551282+00:00
-- url     : https://prove2.me/submissions/ed4ba323-8520-4384-8497-c2b9bf4d7fa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Random coefficients in each finite time-mark cell integrate exactly
against the original Levy time-intensity compensator, path by path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
      (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂(timeMeasure.prod X.ν)) =
    ∑ i ∈ S, H i ω *
      (timeMeasure.prod X.ν)
        (Ioc (s i) (t i) ×ˢ B i) := by
  have hm (i : ι) (hi : i ∈ S) : Measurable
      (fun p : ℝ≥0 × ℝ =>
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p) :=
    measurable_const.indicator (measurableSet_Ioc.prod (hB i hi))
  rw [lintegral_finset_sum S hm]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const
    (measurableSet_Ioc.prod (hB i hi)) (H i ω)
