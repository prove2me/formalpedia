-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:53:05.81245+00:00
-- url     : https://prove2.me/submissions/2d31fa93-6abe-4cd4-b94c-679168ab18fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hj : Measurable j := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hpos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hnonzero : MeasurableSet {u : ℝ≥0 | j u ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hS : MeasurableSet {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} :=
    hpos.inter hnonzero
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) :=
    Measurable.prodMk measurable_id hj
  change (∫⁻ p, f p ∂
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then f (u, j u) else 0
  rw [lintegral_map hf hF]
  rw [← lintegral_indicator hS (fun u : ℝ≥0 => f (u, j u))]
  rw [lintegral_count]
  apply tsum_congr
  intro u
  by_cases hu : 0 < u ∧ j u ≠ 0
  · simp [Set.indicator, hu]
  · simp [Set.indicator, hu]
