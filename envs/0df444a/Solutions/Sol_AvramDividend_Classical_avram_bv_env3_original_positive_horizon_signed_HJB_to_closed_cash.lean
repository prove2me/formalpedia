-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:56:13.786094+00:00
-- url     : https://prove2.me/submissions/53429594-ea94-455f-811e-4bd18778caec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hSigned :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
      else 0) ∂P) ≤ w x) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
    else 0
  have hTermI : Integrable Term P := by
    simpa only [Term, S] using
      (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
        X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
        x D hD T hT hTpos).1
  have hTermNonneg : ∀ ω, 0 ≤ Term ω := by
    intro ω
    dsimp [Term]
    split_ifs with hSurvive
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
          X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
          x hx hxc D hD ω S)
    · exact le_refl 0
  have hBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
    simpa only [Term, S] using hSigned
  exact avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
    X x C D hD q hq T hT (w x)
    Term hTermI hTermNonneg hBudget
