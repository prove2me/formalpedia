-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:17:24.022339+00:00
-- url     : https://prove2.me/submissions/e6254cfc-f153-4362-b8a9-651c039516b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Every cofinal family of original stopped clocks exhausts the exact pre-ruin paying set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ)
    (σ : ℕ → ℝ≥0∞)
    (hSup : (⨆ k : ℕ, σ k) = ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ⋃ k : ℕ, (paymentTimes (σ k) ∩ Iic T) := by
  classical
  ext t
  simp only [paymentTimes, mem_inter_iff, mem_iUnion, mem_setOf_eq, mem_Iic]
  constructor
  · rintro ⟨⟨ht0, hz | hpre⟩, hT⟩
    · exact ⟨0, ⟨⟨ht0, Or.inl hz⟩, hT⟩⟩
    · rw [← hSup] at hpre
      obtain ⟨k, hk⟩ := (lt_iSup_iff).mp hpre
      exact ⟨k, ⟨⟨ht0, Or.inr hk⟩, hT⟩⟩
  · rintro ⟨k, ⟨⟨ht0, hz | hpre⟩, hT⟩⟩
    · exact ⟨⟨ht0, Or.inl hz⟩, hT⟩
    · have hk : σ k ≤ ruinTime X x D ω := by
        rw [← hSup]
        exact le_iSup σ k
      exact ⟨⟨ht0, Or.inr (lt_of_lt_of_le hpre hk)⟩, hT⟩
