-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_finite_horizon_clock_strict_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:59:57.603784+00:00
-- url     : https://prove2.me/submissions/22479093-c777-4db2-aca4-ecea5f499df7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A deterministic clock strictly after T does not alter any positive payment time
before T; the special initial right-payment is retained even if ruin is immediate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) :
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T := by
  classical
  ext t
  constructor
  · rintro ⟨htPay, htT⟩
    change 0 ≤ t ∧
      (t = 0 ∨ ENNReal.ofReal t < min (ruinTime X x D ω) (n : ℝ≥0∞)) at htPay
    rcases htPay with ⟨ht0, hzero | hlt⟩
    · exact ⟨⟨ht0, Or.inl hzero⟩, htT⟩
    · exact ⟨⟨ht0, Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))⟩, htT⟩
  · rintro ⟨htPay, htT⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at htPay
    rcases htPay with ⟨ht0, hzero | hlt⟩
    · exact ⟨⟨ht0, Or.inl hzero⟩, htT⟩
    · have htle : ENNReal.ofReal t ≤ ENNReal.ofReal T :=
        ENNReal.ofReal_le_ofReal htT
      exact ⟨⟨ht0, Or.inr (lt_min hlt (lt_of_le_of_lt htle hn))⟩, htT⟩
