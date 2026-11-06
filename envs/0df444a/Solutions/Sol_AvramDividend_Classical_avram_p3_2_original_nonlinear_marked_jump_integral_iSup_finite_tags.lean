-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_nonlinear_marked_jump_integral_iSup_finite_tags
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:49:02.577182+00:00
-- url     : https://prove2.me/submissions/53465852-7b75-481d-9f20-a018c507acaa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original nonlinear marked Lévy jump integrals are the supremum of their
finite genuine jump-tag sums, with no finite-activity assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ⨆ T : Finset ℝ≥0,
      ∑ t ∈ T,
        if 0 < t ∧ X.X t ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0 then
          F (t, X.X t ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)
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
  rw [lintegral_map hF hMark]
  rw [← lintegral_indicator hSet]
  rw [lintegral_count]
  simpa [Set.indicator] using
    (ENNReal.tsum_eq_iSup_sum (f := fun t : ℝ≥0 =>
      if 0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0 then
        F (t, X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)
      else 0))
