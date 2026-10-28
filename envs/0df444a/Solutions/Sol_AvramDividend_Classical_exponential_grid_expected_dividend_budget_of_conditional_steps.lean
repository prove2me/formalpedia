-- Prove2me | solution 1 for AvramDividend.Classical.exponential_grid_expected_dividend_budget_of_conditional_steps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:07:32.615435+00:00
-- url     : https://prove2.me/submissions/27822d16-b52a-4ee0-ba6b-b3e8030115e9

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_dividend_budget_of_one_step_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Exponentially discounted finite-grid budget from the adapted one-step bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : Filtration ℕ mΩ)
    [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (s : ℕ → ℝ)
    (hCashI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * (s (k + 1) - s k))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω ≤ w (u k ω))
    (n : ℕ) :
    (∑ k ∈ Finset.range n,
       ∫ ω, Real.exp (-(q * s k)) * a k ω ∂P) +
      (∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) ≤
        (∫ ω, Real.exp (-(q * s 0)) * w (u 0 ω) ∂P) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.exp (-(q * s k)) :=
    fun k => le_of_lt (Real.exp_pos _)
  have hfactor : ∀ k : ℕ,
      Real.exp (-(q * s (k + 1))) =
        Real.exp (-(q * s k)) *
          Real.exp (-(q * (s (k + 1) - s k))) := by
    intro k
    rw [← Real.exp_add]
    congr 1
    ring
  exact AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_one_step_bounds
    P 𝓖 u a w
    (fun k => Real.exp (-(q * s k)))
    (fun k => Real.exp (-(q * (s (k + 1) - s k))))
    hnonneg hfactor hCashI hVI hstep n
