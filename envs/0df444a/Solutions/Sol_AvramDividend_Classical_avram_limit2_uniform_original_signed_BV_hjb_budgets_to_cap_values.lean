-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_original_signed_BV_hjb_budgets_to_cap_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:16:44.377762+00:00
-- url     : https://prove2.me/submissions/abaf102f-2c45-47d9-ab09-53c8869b0e76

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Uniform original closed-horizon signed BV budgets give postpayment
    terminal integrability, capped value and the actual unrestricted top cap. -/
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
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
        let S : ℝ≥0 := ⟨T, hT⟩
        Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0)) P) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hPolicy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
        let S : ℝ≥0 := ⟨T, hT⟩
        Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω)
        else 0)) P) ∧
      dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc D hD
    exact avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc D hD (hBudgets x hx hxc D hD)
  have hCapped : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    unfold valueFunctionLe
    exact iSup_le fun D => iSup_le fun hD => (hPolicy x hx hxc D hD).2
  refine ⟨?_, hCapped, ?_⟩
  · intro x hx hxc D hD
    exact (hPolicy x hx hxc D hD).1
  · intro hTop x hx
    subst C
    simpa only [valueFunctionLe_top_eq_valueFunction] using
      hCapped x hx le_top
