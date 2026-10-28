-- Prove2me | solution 1 for AvramDividend.Classical.exponential_levy_time_grid_dividends_le_initial_of_terminal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:53:12.597679+00:00
-- url     : https://prove2.me/submissions/53989166-e2e6-471b-bcd2-df6c2aa8e2d5

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_sampled_levy_filtration_exists_of_monotone_grid
import Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividends_le_initial_of_terminal_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Apply the discounted dividend grid budget on the sampled Lévy filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * a k ω) P)
    (hVI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * ((s (k + 1) : ℝ) - (s k : ℝ)))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤ w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n,
      ∫ ω, Real.exp (-(q * (s k : ℝ))) * a k ω ∂P) ≤ w x := by
  obtain ⟨𝓖, h𝓖, hσ⟩ :=
    AvramDividend.Classical.sampled_levy_filtration_exists_of_monotone_grid
      P 𝓕 s hs
  letI : SigmaFiniteFiltration P 𝓖 := hσ
  have hzero : (s 0 : ℝ) = 0 := by simp [hs0]
  have hsteps : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * ((s (k + 1) : ℝ) - (s k : ℝ)))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω ≤ w (u k ω) := by
    intro k
    simpa only [h𝓖 k] using hstep k
  exact
    AvramDividend.Classical.exponential_grid_expected_dividends_le_initial_of_terminal_nonneg
      P 𝓖 u a w q (fun k => (s k : ℝ)) x
      hzero hu0 hCashI hVI hsteps n hterminal
