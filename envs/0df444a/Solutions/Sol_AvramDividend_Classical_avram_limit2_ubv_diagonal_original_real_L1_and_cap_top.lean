-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_diagonal_original_real_L1_and_cap_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:57:16.952834+00:00
-- url     : https://prove2.me/submissions/d6799caf-215f-495a-8ab2-a51b70963751

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_diagonal_natural_clock_all_values
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_value_bound_to_real_expected_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original UBV diagonal stopped cash bounds force real perpetual L1,
    its exact real expectation, and both capped and unrestricted values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hDiag : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (m : ℕ), 0 < x →
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic (m : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D = ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hValue := avram_limit2_ubv_diagonal_natural_clock_all_values
    X hBV q w C hw0 hDiag
  refine ⟨?_, hValue.1, hValue.2⟩
  intro x hx hxc D hD
  exact avram_limit2_capped_value_bound_to_real_expected_cash
    X q x C (w x) (hw x hx hxc) (hValue.1 x hx hxc) D hD
