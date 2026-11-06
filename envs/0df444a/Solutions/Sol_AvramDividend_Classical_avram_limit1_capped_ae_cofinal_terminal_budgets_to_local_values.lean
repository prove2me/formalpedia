-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:01:36.292193+00:00
-- url     : https://prove2.me/submissions/0df1bd5c-5dbb-468b-9dfb-d58f8578e3d8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform a.s.-cofinal stopped cash and nonnegative-terminal budgets control
    both capped and top-cap values without a terminal-vanishing assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
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
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxC D hD
  obtain ⟨σ, hσmeas, hσmono, hSup, Terminal, hStopped⟩ :=
    hBudget x hx hxC D hD
  apply dividendValue_le_of_uniform_truncated_bounds
    X q x D hD.1 (ENNReal.ofReal (w x))
  intro n
  exact avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
    X q x (n : ℝ) D hD.1.1 σ hσmeas hσmono hSup
    Terminal (ENNReal.ofReal (w x)) (hStopped n)
