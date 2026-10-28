-- Prove2me | solution 2 for AvramDividend.Classical.upExitTime_zero_implies_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:26:13.936992+00:00
-- url     : https://prove2.me/submissions/7cfdaa94-b749-4eb9-882b-0451ec1077ba

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
    (h0 : twoSidedExitUpTime X b ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω := by
  intro ε hε
  have h : twoSidedExitUpTime X b ω < (ε : ℝ≥0∞) := by
    rw [h0]
    exact_mod_cast hε
  unfold twoSidedExitUpTime at h
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 h
  obtain ⟨hp, ht'⟩ := iInf_lt_iff.1 ht
  exact ⟨t, by exact_mod_cast ht', hp⟩
