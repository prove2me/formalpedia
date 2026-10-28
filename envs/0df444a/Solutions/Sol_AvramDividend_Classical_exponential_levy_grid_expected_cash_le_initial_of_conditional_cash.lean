-- Prove2me | solution 1 for AvramDividend.Classical.exponential_levy_grid_expected_cash_le_initial_of_conditional_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:04:38.537984+00:00
-- url     : https://prove2.me/submissions/3149482b-4d23-4328-b90c-fec4afaea798

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_sampled_levy_filtration_exists_of_monotone_grid
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_cash_steps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Expected discounted future-dependent interval cash under conditional HJB steps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
          Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) ≤ w x := by
  obtain ⟨𝓖, h𝓖, hσ⟩ :=
    AvramDividend.Classical.sampled_levy_filtration_exists_of_monotone_grid
      P 𝓕 s hs
  letI : SigmaFiniteFiltration P 𝓖 := hσ
  have hsteps : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓖 k]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓖 k]) ω ≤
          Real.exp (-(q * (s k : ℝ))) * w (u k ω) := by
    intro k
    simpa only [h𝓖 k] using hstep k
  have hstart :
      (∫ ω, Real.exp (-(q * (s 0 : ℝ))) * w (u 0 ω) ∂P) = w x := by
    have hae :
        (fun ω => Real.exp (-(q * (s 0 : ℝ))) * w (u 0 ω)) =ᵐ[P]
          (fun _ : Ω => w x) := by
      filter_upwards [hu0] with ω h
      simp [hs0, h]
    rw [integral_congr_ae hae]
    simp
  have hbudget :=
    AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_cash_steps
      P 𝓖 cash
      (fun k ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω))
      hCashI hVI hsteps n
  rw [hstart] at hbudget
  linarith
