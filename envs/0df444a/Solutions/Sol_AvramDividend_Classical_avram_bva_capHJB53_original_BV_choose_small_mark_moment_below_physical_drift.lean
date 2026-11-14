-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB53_original_BV_choose_small_mark_moment_below_physical_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T15:54:50.449229+00:00
-- url     : https://prove2.me/submissions/3842f031-6d4a-478c-a858-e398e3576cd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hd : 0 < X.drift)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∃ n : ℕ, 0 < ε n ∧
      (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) < X.drift := by
  have hSmall := avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
    X hBV hd (0 : ℝ) ε hε hεlim
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hSmall
  refine ⟨N, (hε N).1, ?_⟩
  simpa only [zero_mul, zero_add] using hN N le_rfl
