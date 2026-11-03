-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:41:44.382901+00:00
-- url     : https://prove2.me/submissions/35405c1a-1449-4792-8f95-83883a7c44b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact original payment region at immediate ruin/time zero, as well as
    strictly pre-ruin stops, retaining the initial right dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      Icc (0 : ℝ) (τ ω : ℝ) := by
  rcases hPre with hzero | hStrict
  · rw [hzero]
    ext t
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      exact ⟨⟨ht.1, Or.inl (le_antisymm ht.2 ht.1)⟩, ht.2⟩
  · exact avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
      X x D ω τ hStrict
