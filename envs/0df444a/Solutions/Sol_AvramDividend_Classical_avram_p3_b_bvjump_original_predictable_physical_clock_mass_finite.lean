-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:27:27.861764+00:00
-- url     : https://prove2.me/submissions/db84ca28-6feb-493f-9df2-e8aa868f0bc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original predictable-clock intensity has finite mass on a finite horizon. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P) A) : μ Set.univ < ∞ := by
  let clock := ((volume : Measure ℝ).restrict
    (Icc 0 (T : ℝ))).map Real.toNNReal
  have hclock : clock Set.univ < ∞ :=
    avram_p3_b_bvjump_original_physical_clock_total_mass_finite T
  calc
    μ Set.univ = (clock.prod P) Set.univ :=
      hμclock Set.univ MeasurableSet.univ
    _ = clock Set.univ * P Set.univ := by
      rw [show (Set.univ : Set (ℝ≥0 × Ω)) =
        (Set.univ : Set ℝ≥0) ×ˢ (Set.univ : Set Ω) from by simp]
      rw [Measure.prod_prod]
    _ < ∞ := by simpa using hclock
