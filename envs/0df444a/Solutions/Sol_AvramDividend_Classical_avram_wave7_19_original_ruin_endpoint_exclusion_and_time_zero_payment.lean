-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:54:24.180787+00:00
-- url     : https://prove2.me/submissions/99c0c2ae-7137-466e-929c-e18fe10cac2d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- At the original ruin boundary the time-zero payment atom survives;
a positive payment exactly at ruin cannot occur. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (0 : ℝ) ∈ paymentTimes (ruinTime X x D ω) ∧
    (∀ t : ℝ, 0 < t → ENNReal.ofReal t = ruinTime X x D ω →
      t ∉ paymentTimes (ruinTime X x D ω)) := by
  constructor
  · change (0 : ℝ) ≤ 0 ∧
      ((0 : ℝ) = 0 ∨ ENNReal.ofReal 0 < ruinTime X x D ω)
    exact ⟨le_refl _, Or.inl rfl⟩
  · intro t ht hruin hpay
    change 0 ≤ t ∧
      (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at hpay
    rcases hpay.2 with hzero | hbefore
    · exact (ne_of_gt ht) hzero
    · rw [hruin] at hbefore
      exact (lt_irrefl _ hbefore)
