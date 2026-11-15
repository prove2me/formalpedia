-- Prove2me | solution 1 for AvramDividend.Classical.avram_b93_original_finite_activity_signed_small_mark_cutoff_limit_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:13:07.355721+00:00
-- url     : https://prove2.me/submissions/9f62d244-8b2f-4aa2-b017-eebce4317ac7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Existing original finite-activity first-mark cutoff convergence is the exact statement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by
  exact avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit X hFinite
