-- Prove2me | solution 2 for AvramDividend.Classical.avram_limit2_capped_ae_cofinal_all_strategies_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:57:11.865569+00:00
-- url     : https://prove2.me/submissions/70d2875b-812a-4cac-be20-58562fc0cb2f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform a.e.-cofinal stopped cash budgets give original real L1 payouts
    for every capped admissible strategy, including the top-cap value bound. -/
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
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
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
  obtain ⟨hCappedBound, hTopBound⟩ :=
    avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
      X q w C hBudget
  refine ⟨?_, hCappedBound, hTopBound⟩
  intro x hx hxc D hD
  have hValueLe : dividendValue X q x D ≤ valueFunctionLe X q C x := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  have hValueBound : dividendValue X q x D ≤ ENNReal.ofReal (w x) :=
    hValueLe.trans (hCappedBound x hx hxc)
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValueBound ENNReal.ofReal_lt_top
  obtain ⟨hL1, hIdentity⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1.1 q hFinite
  refine ⟨hL1, hIdentity, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (hw_nonneg x hx hxc)).mp
  simpa only [hIdentity] using hValueBound
