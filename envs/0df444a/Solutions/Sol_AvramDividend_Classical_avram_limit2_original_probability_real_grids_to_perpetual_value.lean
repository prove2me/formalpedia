-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_probability_real_grids_to_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:23:29.681632+00:00
-- url     : https://prove2.me/submissions/ef590331-93b0-4c8e-adef-c90fef8afc31

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Probability-normalised original signed grids at positive horizons
    bound the full perpetual dividend value with exact stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ)
    (hGrids : ∀ n : ℕ, ∃ Term : Ω → ℝ, ∃ F G : ℕ → Ω → ℝ,
      (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧
      (∀ k, Measurable (F k)) ∧
      (∀ k, Integrable (F k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 ≤ F k ω) ∧
      (∀ k, Integrable (G k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, F k ω ≤ B + G k ω) ∧
      (∀ k, (∫ ω, G k ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal
          (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
          liminf (fun k : ℕ => ENNReal.ofReal (F k ω)) atTop)) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBint : Integrable (fun _ : Ω => B) P := integrable_const B
  have hConst : (∫ ω : Ω, B ∂P) = B := by simp
  apply avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
    X q x D hD (ENNReal.ofReal B)
  intro n
  obtain ⟨Term, F, G, hPos, hFmeas, hFint, hFpos,
    hGint, hPath, hMean, hFatou⟩ := hGrids n
  refine ⟨(fun ω => ENNReal.ofReal (Term ω)), ?_⟩
  have hT : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  exact avram_limit2_original_signed_residual_grid_to_actual_cash_terminal_expected_budget
    X q hq x D hD.1 (((n + 1 : ℕ) : ℝ)) hT
    Term F G B hFmeas hFint hFpos hGint
    hBint hConst hPath hMean hFatou hPos
