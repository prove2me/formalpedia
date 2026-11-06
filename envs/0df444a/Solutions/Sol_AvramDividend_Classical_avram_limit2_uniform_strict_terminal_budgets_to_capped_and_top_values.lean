-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_strict_terminal_budgets_to_capped_and_top_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:11:32.143504+00:00
-- url     : https://prove2.me/submissions/99731d96-1ab6-4079-ae31-288d64be2e6c

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

/-- Uniform original strict positive-horizon cash and ENNReal terminal budgets
    imply capped and top-cap unrestricted perpetual value upper bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iio (((n + 1 : ℕ) : ℝ)),
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
  have hCast : (n : ℝ) < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.lt_succ_self n
  have hCash :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hCast⟩
  have hPlus :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
    apply lintegral_mono
    intro ω
    exact le_add_of_nonneg_right bot_le
  exact hCash.trans (hPlus.trans hBudgetN)
