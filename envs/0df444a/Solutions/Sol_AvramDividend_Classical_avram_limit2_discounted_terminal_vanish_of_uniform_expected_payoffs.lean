-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:22:57.654087+00:00
-- url     : https://prove2.me/submissions/a8d3a394-3fa2-403a-84a3-dca1dd2f1915

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit2_discount_factor_tendsto_zero_positive_rate
import Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_vanish_of_uniform_integrable_payoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-! Positive rate combined with uniformly bounded expected stopped payoffs. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 0 < q)
    (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤) :
    Filter.Tendsto (fun n => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  exact AvramDividend.Classical.avram_limit2_terminal_vanish_of_uniform_integrable_payoff
    P (fun n => ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))))
    Payoff Terminal hPayoff hBound M hUniform hFinite
    (AvramDividend.Classical.avram_limit2_discount_factor_tendsto_zero_positive_rate q hq)
