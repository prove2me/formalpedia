-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:33:12.754673+00:00
-- url     : https://prove2.me/submissions/a37f70d8-0b92-42fd-a082-e0c03b2d15b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_halfopen_marked_count_lintegral_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Lévy marked-jump measure admits weighted finite-cell
    additivity on the actual path, including an adjacent contact cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ I)).map
        (fun u : ℝ≥0 => (u, Δ u))
    (∫⁻ p, F p ∂N (Ioc a c)) =
      (∫⁻ p, F p ∂N (Ioc a b)) +
        (∫⁻ p, F p ∂N (Ioc b c)) := by
  have hpair : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    measurable_id.prodMk measurable_const
  have hΔ : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hpair
  have hMark : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hΔ
  have hSet : MeasurableSet {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} :=
    AvramDividend.Classical.avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  dsimp only
  exact AvramDividend.Classical.avram_p3_2_halfopen_marked_count_lintegral_add
      {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
      hSet
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
      hMark F hF a b c hab hbc
