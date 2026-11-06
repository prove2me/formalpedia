-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_residual_grid_to_strict_fatou_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:35:52.155015+00:00
-- url     : https://prove2.me/submissions/1aea3341-6ba2-45e8-8760-1bb5c6355df3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_residual_expected_bound_with_integrable_constant
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_real_grid_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Exact original signed strict cash expected budget from finite-grid
    pathwise residual control, real integrability and Fatou convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F G : ℕ → Ω → ℝ) (B : ℝ)
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
        liminf (fun n : ℕ => ENNReal.ofReal (F n ω)) atTop) :
    (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤
          ENNReal.ofReal B := by
  have hGridMean : ∀ n, (∫ ω, F n ω ∂P) ≤ B := by
    intro n
    exact avram_limit2_signed_grid_residual_expected_bound_with_integrable_constant
      (F n) (G n) B (hFint n) (hGint n)
      hBint hConst (hGridPath n) (hResidualMean n)
  exact avram_limit2_original_signed_strict_real_grid_expected_budget
    X q x T D Term F B hFmeas hFint hFpos hGridMean hFatou
