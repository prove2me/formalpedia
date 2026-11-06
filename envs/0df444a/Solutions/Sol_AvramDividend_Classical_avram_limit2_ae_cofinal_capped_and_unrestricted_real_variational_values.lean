-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ae_cofinal_capped_and_unrestricted_real_variational_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:48:12.850326+00:00
-- url     : https://prove2.me/submissions/a7bb6333-9bf7-4a26-973e-12e6e2443b53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_ae_cofinal_all_strategies_real_L1
import Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_capped_value_exact_real_variational_sup
import Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_unrestricted_value_exact_real_variational_sup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original a.e.-cofinal stopped budgets give exact real perpetual
    variational values across capped reserves and at the unrestricted cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_nonneg : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ σ : ℕ → Ω → ℝ≥0∞,
          (∀ k : ℕ, Measurable (σ k)) ∧
          (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
          (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
          ∃ Terminal : ℕ → Ω → ℝ≥0∞,
            ∀ n k : ℕ,
              (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)) +
                Terminal k ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x =
        ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissibleLe X x C D),
          ENNReal.ofReal
            (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x =
        ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
          ENNReal.ofReal
            (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) := by
  obtain ⟨_, hCappedBound, hTopBound⟩ :=
    avram_limit2_capped_ae_cofinal_all_strategies_real_L1
      X q w C hw_nonneg hBudget
  constructor
  · intro x hx hxc
    have hFinite : valueFunctionLe X q C x < ⊤ :=
      lt_of_le_of_lt (hCappedBound x hx hxc) ENNReal.ofReal_lt_top
    exact (avram_limit2_finite_capped_value_exact_real_variational_sup
      X q x C hFinite).2
  · intro hC x hx
    have hFinite : valueFunction X q x < ⊤ :=
      lt_of_le_of_lt (hTopBound hC x hx) ENNReal.ofReal_lt_top
    exact (avram_limit2_finite_unrestricted_value_exact_real_variational_sup
      X q x hFinite).2
