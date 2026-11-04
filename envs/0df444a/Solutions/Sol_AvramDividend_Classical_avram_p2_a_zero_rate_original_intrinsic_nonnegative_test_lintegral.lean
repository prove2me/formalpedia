-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:08:18.417059+00:00
-- url     : https://prove2.me/submissions/9b12368b-ad97-4c25-8ce8-d3af8c6c29d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_count_restrict_map_test_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every nonnegative measurable original-process jump test is the actual sum
of its marks, with no compensator or rate hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        ({v : ℝ≥0 | 0 < v ∧
          X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).indicator
          (fun v => g (v, X.X v ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v)) u := by
  have hslice : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hdelta : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hslice
  have hmark : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hdelta
  have hJ : MeasurableSet {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable X ω hmark
  exact avram_p2_a_zero_rate_count_restrict_map_test_lintegral _ hJ _ hmark g hg
