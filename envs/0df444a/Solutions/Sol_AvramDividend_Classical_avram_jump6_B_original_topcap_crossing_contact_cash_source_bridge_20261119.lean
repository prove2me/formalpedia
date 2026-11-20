-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:41:34.975436+00:00
-- url     : https://prove2.me/submissions/6bc98cee-3fa8-46c5-b2bb-c39d4da48b6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (ρ δ a : ℝ≥0)
    (hleft : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hbefore : a < ρ)
    (w : ℝ → ℝ) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
       (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
         Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  exact avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
    X x D ω q ρ δ a hleft hbefore.le
    (avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
      X x C D hD hDstrat ω a ρ hbefore)
    w C hTop hw0 hw_cont hw_neg hw_grad
    (ne_of_lt (avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
      X x D hDstrat ω ρ δ q hq))
