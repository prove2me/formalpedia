-- Prove2me | solution 1 for AvramDividend.Classical.negative_near_zero_of_twoSidedExitDownTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:11:17.00385+00:00
-- url     : https://prove2.me/submissions/ef5eef7f-e425-4249-8fdd-a2b21a32c8e5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (h0 : twoSidedExitDownTime X 0 ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by 
  intro ε hε
  have h : twoSidedExitDownTime X 0 ω < (ε : ℝ≥0∞) := by rw [h0]; exact_mod_cast hε
  unfold twoSidedExitDownTime at h
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 h
  obtain ⟨hp, ht'⟩ := iInf_lt_iff.1 ht
  exact ⟨t, by exact_mod_cast ht', hp⟩
