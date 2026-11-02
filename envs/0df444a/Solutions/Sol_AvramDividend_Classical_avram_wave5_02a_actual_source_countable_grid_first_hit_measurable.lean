-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:33:16.169874+00:00
-- url     : https://prove2.me/submissions/46e86d5a-6c15-4635-9735-df7bbe234d98

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (s : ℝ≥0) (a : ℝ) :
    Measurable (fun ω : Ω => ⨅ n : ℕ,
      {ω : Ω | s < grid n ∧ X.X (grid n) ω < a}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω) := by
  apply Measurable.iInf
  intro n
  have hx : Measurable (fun ω => X.X (grid n) ω) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hs : MeasurableSet {ω : Ω | s < grid n ∧ X.X (grid n) ω < a} := by
    by_cases h : s < grid n
    · simpa [h] using (measurableSet_lt hx measurable_const)
    · simp [h]
  exact measurable_const.piecewise hs measurable_const
