-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_original_grid_to_cap_and_top_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:47:45.369206+00:00
-- url     : https://prove2.me/submissions/2fef54f1-4969-4643-a422-4ea9c8f03ec7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_cap_source_grid_exact_real_cash
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Uniform original finite-grid certificates imply capped and unrestricted
    perpetual value bounds while certifying genuine real-cash integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hGridProducers : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) →
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))) →
      ∀ (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T),
      ∃ F M J : ℕ → Ω → ℝ,
        (∀ n, Measurable (F n)) ∧
        (∀ n, Integrable (F n) P) ∧
        (∀ n, 0 ≤ᵐ[P] F n) ∧
        (∀ n, Integrable (fun ω => M n ω + J n ω) P ∧
          (∫ ω, M n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n ω + J n ω)) ∧
        (∀ᵐ ω ∂P,
          let S : ℝ≥0 := ⟨T, hT⟩
          ENNReal.ofReal
            ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)).toReal +
              (if (S : ℝ≥0∞) < ruinTime X x D ω then
                Real.exp (-(q * T)) * w (riskProcess X x D S ω)
              else 0)) ≤
            liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    unfold valueFunctionLe
    exact iSup_le fun D => iSup_le fun hD =>
      (avram_limit2_original_positive_cap_source_grid_exact_real_cash
        X q hq w C hC hw_cont hw0 hw_smooth hw_grad
        x hx hxc D hD (hGridProducers x hx hxc D hD)).1
  refine ⟨hCap, ?_⟩
  intro hTop x hx
  subst C
  simpa only [valueFunctionLe_top_eq_valueFunction] using
    hCap x hx le_top
