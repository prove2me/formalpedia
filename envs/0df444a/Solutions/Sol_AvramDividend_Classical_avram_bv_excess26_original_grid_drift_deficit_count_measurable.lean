-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess26_original_grid_drift_deficit_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:26:49.072403+00:00
-- url     : https://prove2.me/submissions/0fbbae52-6ca8-41ad-b995-7d193e924160

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every drift-deficient original physical grid cell is a measurable event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if X.X (u (i + 1)) ω - X.X (u i) ω <
           X.drift * (((u (i + 1) - u i : ℝ≥0) : ℝ)) then
          (1 : ℝ≥0∞) else 0) := by
  classical
  have hEval : ∀ t : ℝ≥0, Measurable (fun ω : Ω => X.X t ω) := by
    intro t
    exact (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_id)
  apply Finset.measurable_sum
  intro i hi
  have hDiff : Measurable (fun ω : Ω =>
      X.X (u (i + 1)) ω - X.X (u i) ω) :=
    (hEval _).sub (hEval _)
  have hEvent : MeasurableSet {ω : Ω |
      X.X (u (i + 1)) ω - X.X (u i) ω <
        X.drift * (((u (i + 1) - u i : ℝ≥0) : ℝ))} :=
    measurableSet_lt hDiff measurable_const
  exact Measurable.ite hEvent measurable_const measurable_const
