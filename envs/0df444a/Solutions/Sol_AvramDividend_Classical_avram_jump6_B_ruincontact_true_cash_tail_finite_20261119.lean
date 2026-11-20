-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:31:17.181477+00:00
-- url     : https://prove2.me/submissions/d6f48bc0-6320-42da-8997-6e8bc729cbcf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ δ : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) < ⊤ := by
  have hfull :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hDstrat ω (ruinTime X x D ω) ρ q hq
  have hsub :
      paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (ρ : ℝ) := by
    intro s hs
    exact ⟨hs.1, le_of_lt hs.2.2⟩
  exact lt_of_le_of_lt (lintegral_mono_set hsub) hfull
