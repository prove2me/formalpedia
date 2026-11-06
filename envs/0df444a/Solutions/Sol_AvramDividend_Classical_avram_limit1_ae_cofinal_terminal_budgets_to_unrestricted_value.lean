-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:46:30.990277+00:00
-- url     : https://prove2.me/submissions/d38ce295-249e-4f8f-9f31-54b930988665

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original a.s.-cofinal nonnegative-terminal stopped budgets imply the
    unrestricted perpetual dividend value bound without terminal vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (B : ℝ≥0∞)
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
    valueFunction X q x ≤ B := by
  unfold valueFunction
  refine iSup_le fun D => iSup_le fun hD => ?_
  obtain ⟨σ, hσmeas, hσmono, hSup, Terminal, hStopped⟩ :=
    hBudget D hD
  apply dividendValue_le_of_uniform_truncated_bounds X q x D hD B
  intro n
  exact avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
    X q x (n : ℝ) D hD.1 σ hσmeas hσmono hSup Terminal B (hStopped n)
