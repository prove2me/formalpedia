-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:40:50.459605+00:00
-- url     : https://prove2.me/submissions/a3ec681a-2f4b-489a-b25a-174678dd2f14

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuinely controlled post-payment reserve inherits absence of
upward jumps, with both Lévy and right-dividend jumps included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ,
      Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      x + X.X t ω - rightLimit D t ω ≤ l := by
  obtain ⟨l, hleft, hpre⟩ :=
    avram_wave3_04_postPaymentReserve_prejump_upper X x D hD ω t ht
  refine ⟨l, hleft, ?_⟩
  have hpay := dividendStrategy_le_rightLimit D hD ω t
  linarith
