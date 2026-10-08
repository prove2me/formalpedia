-- Prove2me | solution 1 for AvramDividend.Classical.integrableOn_Icc_of_continuousOn_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:04:37.952993+00:00
-- url     : https://prove2.me/submissions/d2f6c31b-ec46-43cd-a49d-434a1bbb3645

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (f : ℝ → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (l u : ℝ) (hlu : l ≤ u)
    (hf : ContinuousOn f (Icc l u)) :
    IntegrableOn f (Icc l u) μ := by
  have hne : (Icc l u).Nonempty := by
    exact ⟨l, ⟨le_rfl, hlu⟩⟩
  obtain ⟨z, hz, hmax⟩ :
      ∃ z ∈ Icc l u, ∀ x ∈ Icc l u, ‖f x‖ ≤ ‖f z‖ :=
    isCompact_Icc.exists_isMaxOn hne hf.norm
  have hmeas :
      AEStronglyMeasurable f (μ.restrict (Icc l u)) :=
    hf.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
  apply IntegrableOn.of_bound (by finiteness) hmeas ‖f z‖
  filter_upwards [self_mem_ae_restrict (μ := μ) measurableSet_Icc] with x hx
  exact hmax x hx
