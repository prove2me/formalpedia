-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_levy_finite_physical_grid_nonlinear_jump_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:45:57.483225+00:00
-- url     : https://prove2.me/submissions/24926f04-71c3-4118-a254-e08ca1301e9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_finite_physical_grid_marked_count_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact finite physical grid partition of the original Lévy nonlinear
marked jump integral, retaining every original mark and endpoint atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict
        ({t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0} ∩
          Set.Ioc (u 0) (u n))).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))) =
      ∑ i ∈ Finset.range n,
        (∫⁻ p, F p ∂
          ((Measure.count.restrict
            ({t : ℝ≥0 | 0 < t ∧
              X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0} ∩
              Set.Ioc (u i) (u (i + 1)))).map
            (fun t : ℝ≥0 => (t,
              X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))) := by
  have hPair : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    measurable_id.prodMk measurable_const
  have hSection : Measurable (fun t : ℝ≥0 =>
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hPair
  have hMark : Measurable (fun t : ℝ≥0 => (t,
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)) :=
    measurable_id.prodMk hSection
  have hSet :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  exact avram_p3_2_finite_physical_grid_marked_count_partition
    _ hSet _ hMark F hF u hmono n
