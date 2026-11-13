-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB184_ae_real_level_zero_singleton_mass_of_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:01:39.020808+00:00
-- url     : https://prove2.me/submissions/f0a16e33-0367-4ead-bec4-4921d1989903

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem solution (μ : Measure ℝ) [SFinite μ] :
    ∀ᵐ y ∂(volume : Measure ℝ), μ {y} = 0 := by
  have hdisj : Pairwise (Function.onFun Disjoint (fun y : ℝ => ({y} : Set ℝ))) := by
    intro y z hyz
    exact Set.disjoint_singleton.mpr hyz
  have hcount : {y : ℝ | 0 < μ {y}}.Countable := by
    exact MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion
      (μ := μ) (As := fun y : ℝ => ({y} : Set ℝ))
      (fun _ => measurableSet_singleton _) hdisj
  have hzero : (volume : Measure ℝ) {y : ℝ | 0 < μ {y}} = 0 :=
    hcount.measure_zero (volume : Measure ℝ)
  have hae : ∀ᵐ y ∂(volume : Measure ℝ),
      y ∉ {y : ℝ | 0 < μ {y}} := by
    apply (ae_iff).2
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  filter_upwards [hae] with y hy
  exact le_antisymm (le_of_not_gt hy) bot_le
