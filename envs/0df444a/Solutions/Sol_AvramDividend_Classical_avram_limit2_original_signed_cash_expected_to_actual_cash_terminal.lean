-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:23:20.562214+00:00
-- url     : https://prove2.me/submissions/3d0719ec-cbdf-445a-b01e-ec182ff46b9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_cash_postterminal_ofreal_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Transfer a genuinely finite original stopped signed-real expected payoff
    to original ENNReal cash plus the nonnegative terminal, AE only. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ) (B : ℝ≥0∞)
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤ B := by
  calc
    _ = (∫⁻ ω, ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hCashFinite, hTermPos] with ω hFinite hTerm
      exact (avram_limit2_original_strict_cash_postterminal_ofreal_exact
        X q x T D ω (Term ω) hTerm hFinite).symm
    _ ≤ B := hExpected
