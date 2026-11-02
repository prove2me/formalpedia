-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:13:54.067927+00:00
-- url     : https://prove2.me/submissions/ee05730d-c5f6-4b53-a41d-72873f4e0805

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ≥0∞) (hTa : ENNReal.ofReal T < a) :
    ∀ ω, paymentTimes (min (ruinTime X x D ω) a) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T := by
  intro ω
  ext t
  change
    ((0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t <
      min (ruinTime X x D ω) a)) ∧ t ≤ T) ↔
    ((0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t <
      ruinTime X x D ω)) ∧ t ≤ T)
  constructor
  · rintro ⟨⟨ht0, hpay⟩, htT⟩
    refine ⟨⟨ht0, ?_⟩, htT⟩
    rcases hpay with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
  · rintro ⟨⟨ht0, hpay⟩, htT⟩
    refine ⟨⟨ht0, ?_⟩, htT⟩
    rcases hpay with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr (lt_min hlt
        (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htT) hTa))
end
