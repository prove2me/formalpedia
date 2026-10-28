-- Prove2me | solution 1 for AvramDividend.Classical.positive_near_zero_of_twoSidedExitUpTime_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:11:17.437729+00:00
-- url     : https://prove2.me/submissions/26fddb5a-ca3e-41f1-b9ec-3087eccb8402

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (h0 : twoSidedExitUpTime X 0 ω = 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by 
  intro ε hε
  have h : twoSidedExitUpTime X 0 ω < (ε : ℝ≥0∞) := by rw [h0]; exact_mod_cast hε
  unfold twoSidedExitUpTime at h
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 h
  obtain ⟨hp, ht'⟩ := iInf_lt_iff.1 ht
  exact ⟨t, by exact_mod_cast ht', hp⟩
