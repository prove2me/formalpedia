-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_postpayment_reserve_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:19:22.606724+00:00
-- url     : https://prove2.me/submissions/f422eb7b-6dac-4079-9474-ad80a848b8d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_no_positive_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    (∀ (t : ℝ≥0),
      ContinuousWithinAt
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (Ici t) t) ∧
    (∀ (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l)) := by
  constructor
  · intro t
    exact (continuousWithinAt_const.add (X.rightCont ω t)).sub
      (dividendStrategy_rightLimit_rightContinuous D hD ω t)
  · intro t ht
    obtain ⟨l, hl, _⟩ :=
      avram_wave3_04_postPaymentReserve_no_positive_jumps X x D hD ω t ht
    exact ⟨l, hl⟩