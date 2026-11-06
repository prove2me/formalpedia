-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_strict_real_grid_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:25:38.986368+00:00
-- url     : https://prove2.me/submissions/4389b238-d7bd-406f-89ad-332f3315e929

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Exact original signed strict cash-to-real expected budget from
    a genuinely integrable nonnegative real grid and source Fatou certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F : ℕ → Ω → ℝ) (B : ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hGridMean : ∀ n, (∫ ω, F n ω ∂P) ≤ B)
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
  have hMeas : ∀ n : ℕ,
      Measurable (fun ω => ENNReal.ofReal (F n ω)) := by
    intro n
    exact (hFmeas n).ennreal_ofReal
  have hMean : ∀ n : ℕ,
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal B :=
    avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
      F B hFint hFpos hGridMean
  exact avram_limit2_original_signed_strict_fatou_real_grid_certificate
    X q x T D Term (fun n ω => ENNReal.ofReal (F n ω))
    (ENNReal.ofReal B) hMeas hMean hFatou
