-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:17:58.639482+00:00
-- url     : https://prove2.me/submissions/9ef96e4f-3417-4ddc-90ca-624e44799eb5

import Mathlib
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

/-- Positive/negative original signed-kernel count integrals on an actual
half-open physical clock cell, including every genuine original jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let Nst : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} ∩
          Set.Ioc s t)).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, ENNReal.ofReal (F p) ∂Nst) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
          u ∈ Set.Ioc s t then
          ENNReal.ofReal (F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) ∧
    ((∫⁻ p, ENNReal.ofReal (-F p) ∂Nst) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
          u ∈ Set.Ioc s t then
          ENNReal.ofReal (-F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) := by
  have hPair : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hSection : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hPair
  have hMark : Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hSection
  have hJumps :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  have hCell : MeasurableSet
      ({u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} ∩
        Set.Ioc s t) := hJumps.inter measurableSet_Ioc
  dsimp
  constructor
  · simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using
      (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
        _ hCell _ hMark (fun p => ENNReal.ofReal (F p))
        (ENNReal.measurable_ofReal.comp hF))
  · simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using
      (avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
        _ hCell _ hMark (fun p => ENNReal.ofReal (-F p))
        (ENNReal.measurable_ofReal.comp hF.neg))
