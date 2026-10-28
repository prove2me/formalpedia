-- Prove2me | solution 1 for AvramDividend.Classical.upExitTime_zero_implies_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:25:50.164466+00:00
-- url     : https://prove2.me/submissions/004bae25-02f1-4268-adc5-1f6a5075bd3b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (h0 : twoSidedExitUpTime X b ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω := by 
  intro ε hε
  have h : twoSidedExitUpTime X b ω < (ε : ℝ≥0∞) := by rw [h0]; exact_mod_cast hε
  unfold twoSidedExitUpTime at h
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 h
  obtain ⟨hp, ht'⟩ := iInf_lt_iff.1 ht
  exact ⟨t, by exact_mod_cast ht', hp⟩
