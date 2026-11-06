-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:59:42.095612+00:00
-- url     : https://prove2.me/submissions/fad58c8f-23e8-4c3d-b9ec-11ff5f9c22e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Signed-real original strict stopped budget transfers to actual ENNReal
    cash using admitted pathwise Stieltjes finiteness, without extra hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T) (Term : Ω → ℝ) (B : ℝ≥0∞)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤ B := by
  have hFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≠ ⊤ := by
    exact Filter.Eventually.of_forall (fun ω =>
      avram_limit2_original_strict_discounted_cash_finite_all_paths
        X q hq x D hD ω T hT)
  exact avram_limit2_original_signed_cash_expected_to_actual_cash_terminal
    X q x T D Term B hFinite hTermPos hExpected
