-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_signed_terminal_real_budgets_to_capped_and_unrestricted_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:22:04.601776+00:00
-- url     : https://prove2.me/submissions/fc12c8a6-b472-4222-9279-0835331575c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Real signed original Stieltjes budgets with nonnegative terminal means
    pass to genuine capped and unrestricted perpetual dividend values. -/
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
          ((∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) +
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
  have hMean : (0 : ℝ) ≤ ∫ ω, Terminal ω ∂P :=
    integral_nonneg_of_ae hTermNonneg
  linarith only [hMean, hJoint]
