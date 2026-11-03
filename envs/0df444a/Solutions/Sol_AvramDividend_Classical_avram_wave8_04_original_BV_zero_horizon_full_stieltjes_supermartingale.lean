-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_zero_horizon_full_stieltjes_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:34:05.161447+00:00
-- url     : https://prove2.me/submissions/56d73912-0013-43b5-b591-c4e813fb6c07

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_strict_survival_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
    let Term : Ω → ℝ := fun ω =>
      if (0 : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (w (x - rightLimit D 0 ω))
      else 0
    Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  classical
  dsimp
  have hCashI : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
    simpa using
      (avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
        X x C D hD q (fun _ : Ω => (0 : ℝ≥0)) 0
        measurable_const (fun _ => le_rfl))
  have hTermI : Integrable (fun ω : Ω =>
      if (0 : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (w (x - rightLimit D 0 ω)) else 0) P := by
    convert avram_wave8_04_original_BV_strict_survival_terminal_integrable
      X hBV q w hw_cont hw_neg x D hD.1.1 (0 : ℝ≥0) using 1
    funext ω
    simp [X.X_zero]
  exact ⟨hTermI,
    avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD hjump q hCashI hTermI⟩
