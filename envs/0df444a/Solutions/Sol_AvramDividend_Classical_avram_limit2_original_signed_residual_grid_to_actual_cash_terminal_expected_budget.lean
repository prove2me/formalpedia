-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:07:53.387467+00:00
-- url     : https://prove2.me/submissions/de8bc02c-3a2c-47b4-a1f9-6438d54e145b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Complete source-exact original BV real compensated grid and strict
    Stieltjes Fatou budget to actual ENNReal cash plus terminal bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T)
    (Term : Ω → ℝ) (F G : ℕ → Ω → ℝ) (B : ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hGint : ∀ n, Integrable (G n) P)
    (hBint : Integrable (fun _ : Ω => B) P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hGridPath : ∀ n, ∀ᵐ ω ∂P, F n ω ≤ B + G n ω)
    (hResidualMean : ∀ n, (∫ ω, G n ω ∂P) ≤ 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
        liminf (fun n : ℕ => ENNReal.ofReal (F n ω)) atTop)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    (∫⁻ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + ENNReal.ofReal (Term ω) ∂P) ≤
          ENNReal.ofReal B := by
  have hSigned :
      (∫⁻ ω, ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤
            ENNReal.ofReal B :=
    avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
      X q x T D Term F G B hFmeas hFint hFpos
      hGint hBint hConst hGridPath hResidualMean hFatou
  exact avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
    X q hq x D hD T hT Term (ENNReal.ofReal B) hTermPos hSigned
