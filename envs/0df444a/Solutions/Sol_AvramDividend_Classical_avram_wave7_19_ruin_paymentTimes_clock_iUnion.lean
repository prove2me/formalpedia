-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:47:00.603485+00:00
-- url     : https://prove2.me/submissions/6620b357-cef2-4c10-9cc1-98735159fd82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original strict pre-ruin payment domain is exhausted by integer clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ⋃ n : ℕ, paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T := by
  classical
  ext t
  constructor
  · rintro ⟨htPay, htT⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at htPay
    rcases htPay with ⟨ht0, hzero | hlt⟩
    · exact Set.mem_iUnion.mpr ⟨0, ⟨⟨ht0, Or.inl hzero⟩, htT⟩⟩
    · have hfin : ENNReal.ofReal t ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hlt le_top)
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact ⟨⟨ht0, Or.inr (lt_min hlt hn)⟩, htT⟩
  · intro ht
    obtain ⟨n, ⟨htPay, htT⟩⟩ := Set.mem_iUnion.mp ht
    change 0 ≤ t ∧
      (t = 0 ∨ ENNReal.ofReal t < min (ruinTime X x D ω) (n : ℝ≥0∞)) at htPay
    rcases htPay with ⟨ht0, hzero | hlt⟩
    · exact ⟨⟨ht0, Or.inl hzero⟩, htT⟩
    · exact ⟨⟨ht0, Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))⟩, htT⟩
