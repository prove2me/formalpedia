-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_2_original_source_nonlinear_jump_count_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:53:16.484261+00:00
-- url     : https://prove2.me/submissions/1256c028-a45b-47d2-a6cb-94bd96f89d3d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Literal original source nonlinear jump kernel: counting integral equals
the all-time actual original marked-jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
          F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0 := by
  have hPair : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hSection : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hPair
  have hMark : Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hSection
  have hSet :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  simpa only [Set.mem_setOf_eq] using
    (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
      _ hSet _ hMark F hF)
