-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_original_signed_real_cash_and_cap_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:49:02.027615+00:00
-- url     : https://prove2.me/submissions/963bde2f-dfc2-4dee-af06-f02bc72180e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_signed_budget_exact_real_perpetual_mean
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Uniform original signed stopped budgets give L1 real perpetual dividends,
    their exact expected cash, and capped/unrestricted value bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hBudgets : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0) ∂P) ≤ w x) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    unfold valueFunctionLe
    exact iSup_le fun D => iSup_le fun hD =>
      (avram_limit2_original_HJB_signed_budget_exact_real_perpetual_mean
        X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_hjb x hx hxc D hD (hBudgets x hx hxc D hD)).2.1
  refine ⟨?_, hCap, ?_⟩
  · intro x hx hxc D hD
    exact (avram_limit2_original_HJB_signed_budget_exact_real_perpetual_mean
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc D hD (hBudgets x hx hxc D hD)).2.2
  · intro hTop x hx
    subst C
    simpa only [valueFunctionLe_top_eq_valueFunction] using
      hCap x hx le_top
