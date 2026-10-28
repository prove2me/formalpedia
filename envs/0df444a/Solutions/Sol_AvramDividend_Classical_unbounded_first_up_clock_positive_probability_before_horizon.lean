-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_first_up_clock_positive_probability_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:04:01.776293+00:00
-- url     : https://prove2.me/submissions/04ce6b05-b7d4-4434-98e6-950c85f65dd9

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_level_upcrossing_strictly_before_horizon
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For each positive horizon the canonical strict upper first-passage
clock crosses some positive level before the horizon with positive mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧
      0 < P {ω : Ω | twoSidedExitUpTime X a ω < (t : ℝ≥0∞)} := by
  obtain ⟨a, ha, hpositive⟩ :=
    unbounded_positive_level_upcrossing_strictly_before_horizon
      X q hq hnbv t ht
  refine ⟨a, ha, ?_⟩
  have hsub :
      {ω : Ω | ∃ s : ℝ≥0, s < t ∧ a < X.X s ω} ⊆
        {ω : Ω | twoSidedExitUpTime X a ω < (t : ℝ≥0∞)} := by
    intro ω hω
    obtain ⟨s, hs, hlevel⟩ := hω
    have hclock : twoSidedExitUpTime X a ω ≤ (s : ℝ≥0∞) := by
      unfold twoSidedExitUpTime
      exact iInf_le_of_le s (iInf_le_of_le hlevel le_rfl)
    have hstrict : (s : ℝ≥0∞) < (t : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr hs
    exact lt_of_le_of_lt hclock hstrict
  exact lt_of_lt_of_le hpositive (measure_mono hsub)
