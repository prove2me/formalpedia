-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_upcrossing_before_any_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:57:28.470024+00:00
-- url     : https://prove2.me/submissions/7e5956e6-dbb0-41fa-a8e5-87c7970624ed

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure_all_times
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Positive probability of crossing above the initial reserve before
each positive time horizon, under unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    0 < P {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ 0 < X.X s ω} := by
  obtain ⟨β₀, hβ₀, hlarge⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hpos :
      0 < P {ω : Ω | 0 < X.X t ω} :=
    positive_psi_implies_upward_increment_positive_measure_all_times
      X β₀ hβ₀ (lt_trans hq (hlarge β₀ le_rfl)) t ht
  have hsub :
      {ω : Ω | 0 < X.X t ω} ⊆
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ 0 < X.X s ω} := by
    intro ω hω
    exact ⟨t, le_rfl, hω⟩
  exact lt_of_lt_of_le hpos (measure_mono hsub)
