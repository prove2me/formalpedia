-- Prove2me | solution 1 for AvramDividend.Classical.exponential_grid_expected_dividends_le_initial_of_terminal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:11:22.811301+00:00
-- url     : https://prove2.me/submissions/ff5fdb0d-e448-468b-968e-0ec720dabe80

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividend_budget_of_conditional_steps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Drop a nonnegative terminal verification value from the discounted grid budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (s : ℕ → ℝ) (x : ℝ)
    (hs0 : s 0 = 0)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * (s (k + 1) - s k))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω ≤ w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n,
      ∫ ω, Real.exp (-(q * s k)) * a k ω ∂P) ≤ w x := by
  have hstart :
      (∫ ω, Real.exp (-(q * s 0)) * w (u 0 ω) ∂P) = w x := by
    have hae :
        (fun ω => Real.exp (-(q * s 0)) * w (u 0 ω)) =ᵐ[P]
          (fun _ : Ω => w x) := by
      filter_upwards [hu0] with ω h
      simp [hs0, h]
    rw [integral_congr_ae hae]
    simp
  have hbudget :=
    AvramDividend.Classical.exponential_grid_expected_dividend_budget_of_conditional_steps
      P 𝓖 u a w q s hCashI hVI hstep n
  rw [hstart] at hbudget
  linarith
