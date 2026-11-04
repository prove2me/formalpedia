-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_bochner_stieltjes_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:40:41.320411+00:00
-- url     : https://prove2.me/submissions/693fc9fe-e106-404c-add6-07c8c6ecb0cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original P4-F `Cash` field is the ordinary signed-capable Stieltjes integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    Cash ω =
      ∫ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * s)) ∂(dividendMeasure D ω) := by
  rw [hCash ω]
  exact
    avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral
      D hD ω (ruinTime X x D ω) (τ ω) q hq
