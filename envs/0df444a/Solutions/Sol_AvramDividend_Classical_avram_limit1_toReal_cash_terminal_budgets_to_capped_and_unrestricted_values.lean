-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_toReal_cash_terminal_budgets_to_capped_and_unrestricted_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:22:00.903283+00:00
-- url     : https://prove2.me/submissions/137c1598-03ec-4cbf-8b0e-b04677d0be6e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Signed expected stopped original toReal cash plus a nonnegative real
    terminal budget controls the genuine capped and original value functions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ,
          Integrable Terminal P ∧
          (∀ᵐ ω ∂P, 0 ≤ Terminal ω) ∧
          ((∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)).toReal ∂P) +
            (∫ ω, Terminal ω ∂P) ≤ w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_strategy_bound X q w C
  intro x hx hxC D hD
  apply avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
    X x C D hD q hq (w x)
  intro n
  obtain ⟨Terminal, hTermI, hTermNonneg, hJoint⟩ :=
    hBudget x hx hxC D hD n
  have hCashEq :=
    avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
      X x D hD.1.1 q hq (((n + 1 : ℕ) : ℝ)) (by positivity)
  rw [hCashEq] at hJoint
  have hTermMean : (0 : ℝ) ≤ ∫ ω, Terminal ω ∂P :=
    integral_nonneg_of_ae hTermNonneg
  linarith only [hTermMean, hJoint]
