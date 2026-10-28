-- Prove2me | solution 1 for AvramDividend.Classical.downExitTime_zero_implies_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:26:09.476776+00:00
-- url     : https://prove2.me/submissions/405e5efa-518b-45ec-9531-7050ee721dcf

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero first-exit time at any threshold yields arbitrarily early strict crossings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (h0 : twoSidedExitDownTime X b ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b := by
  intro ε hε
  have h : twoSidedExitDownTime X b ω < (ε : ℝ≥0∞) := by
    rw [h0]
    exact_mod_cast hε
  unfold twoSidedExitDownTime at h
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 h
  obtain ⟨hp, ht'⟩ := iInf_lt_iff.1 ht
  exact ⟨t, by exact_mod_cast ht', hp⟩
