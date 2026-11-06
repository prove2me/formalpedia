-- Prove2me | solution 2 for AvramDividend.Classical.avram_limit2_ae_cofinal_unrestricted_real_variational_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:57:19.826121+00:00
-- url     : https://prove2.me/submissions/59a177ec-f6c3-4171-95d3-e0444a361af8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform a.e.-cofinal nonnegative-terminal budgets for every genuine
    original strategy yield the real perpetual variational value identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤)
    (hBudget : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissible X x D →
      ∃ σ : ℕ → Ω → ℝ≥0∞,
        (∀ k : ℕ, Measurable (σ k)) ∧
        (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
        (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
        ∃ Terminal : ℕ → Ω → ℝ≥0∞,
          ∀ n k : ℕ,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) +
              Terminal k ω) ∂P) ≤ B) :
    valueFunction X q x ≤ B ∧
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunction X q x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hBound : valueFunction X q x ≤ B :=
    avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
      X q x B hBudget
  have hFiniteValue : valueFunction X q x < ⊤ :=
    lt_of_le_of_lt hBound hB
  have hExact : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      dividendValue X q x D =
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    intro D hD
    have hValueLe : dividendValue X q x D ≤ valueFunction X q x := by
      unfold valueFunction
      exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
    have hFinite : dividendValue X q x D < ⊤ :=
      lt_of_le_of_lt hValueLe hFiniteValue
    exact avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  refine ⟨hBound, fun D hD => (hExact D hD).1, ?_⟩
  unfold valueFunction
  refine iSup_congr fun D => iSup_congr fun hD => ?_
  exact (hExact D hD).2
