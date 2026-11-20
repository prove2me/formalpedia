-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_topcap_terminal_contact_cash_plus_prefix_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:42:09.784012+00:00
-- url     : https://prove2.me/submissions/18e7a978-a998-4ac8-b40b-941256c8280a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (ρ δ a : ℝ≥0)
    (hρpos : 0 < ρ) (hρruin : (ρ : ℝ≥0∞) = ruinTime X x D ω)
    (hleft : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hbefore : a < ρ)
    (w : ℝ → ℝ) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Real.exp (-(q * (ρ : ℝ))) *
      (w (x + X.X ρ ω - rightLimit D ρ ω) -
       w (x + X.X ρ ω - rightLimit D a ω)) +
    Real.exp (-(q * (ρ : ℝ))) *
      (w (riskProcess X x D ρ ω) -
       w (x + X.X ρ ω - rightLimit D ρ ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (a : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  have hFin :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hDstrat ω (ruinTime X x D ω) ρ q hq
  have hCash :=
    avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
      X x q D ω (a : ℝ) (ρ : ℝ) (by exact_mod_cast (le_of_lt hbefore)) hFin
  have hSet :=
    avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
      (ruinTime X x D ω) ρ hρpos hρruin (a : ℝ)
  rw [hSet] at hCash
  have hCross :=
    avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
      X x C D hD hDstrat ω q hq ρ δ a hleft hbefore
      w hTop hw0 hw_cont hw_neg hw_grad
  rw [hCash]
  nlinarith only [hCross]