-- Prove2me | solution 2 for AvramDividend.Classical.negative_near_zero_of_twoSidedExitDownTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:12:39.345123+00:00
-- url     : https://prove2.me/submissions/448b2930-a6b1-40cd-85bd-6bdb2f602a0c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Instantaneous lower exit implies arbitrarily early negative observations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (h0 : twoSidedExitDownTime X 0 ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by
  intro ε hε
  by_contra h
  have hnone (t : ℝ≥0) (ht : X.X t ω < 0) : ε ≤ t := by
    by_contra hlt
    exact h ⟨t, lt_of_not_ge hlt, ht⟩
  have hbound : (ε : ℝ≥0∞) ≤ twoSidedExitDownTime X 0 ω := by
    unfold twoSidedExitDownTime
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact ENNReal.coe_le_coe.mpr (hnone t ht)
  have hz : (ε : ℝ≥0∞) ≤ 0 := by simpa only [h0] using hbound
  exact (not_le.mpr (ENNReal.coe_pos.mpr hε)) hz
