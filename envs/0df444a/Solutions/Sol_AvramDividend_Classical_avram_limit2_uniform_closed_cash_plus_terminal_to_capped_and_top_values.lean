-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_closed_cash_plus_terminal_to_capped_and_top_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:30:51.997213+00:00
-- url     : https://prove2.me/submissions/a48c11ef-e7cc-4766-8c73-f9518f7d0856

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Closed finite-horizon original cash plus a nonnegative terminal budget
    yields actual capped and top-cap perpetual value bounds at every reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (n : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxc D hD
  rw [dividendValue_eq_iSup_truncated X q x D hD.1]
  refine iSup_le fun n => ?_
  obtain ⟨Terminal, hBudgetN⟩ := hBudget x hx hxc D hD n
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
      apply lintegral_mono
      intro ω
      exact le_add_of_nonneg_right bot_le
    _ ≤ ENNReal.ofReal (w x) := hBudgetN
