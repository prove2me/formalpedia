-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_one_step_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:03:14.658056+00:00
-- url     : https://prove2.me/submissions/62155b2e-edf6-4c88-b494-8d7364005637

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_steps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (α β : ℕ → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hfactor : ∀ k, α (k + 1) = α k * β k)
    (hCashI : ∀ k, Integrable (fun ω => α k * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => α k * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + β k * (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω
        ≤ w (u k ω))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, α k * a k ω ∂P) +
        (∫ ω, α n * w (u n ω) ∂P) ≤
      (∫ ω, α 0 * w (u 0 ω) ∂P) := by
  have hscaled : ∀ k : ℕ, ∀ᵐ ω ∂P,
      α k * a k ω +
          (P[(fun η => α (k + 1) * w (u (k + 1) η)) | 𝓖 k]) ω
        ≤ α k * w (u k ω) := by
    intro k
    have hce :
        P[(fun η => α (k + 1) * w (u (k + 1) η)) | 𝓖 k] =ᵐ[P]
          (fun ω => α (k + 1) *
            (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω) := by
      have hs := MeasureTheory.condExp_smul (μ := P) (α (k + 1))
        (fun η => w (u (k + 1) η)) (𝓖 k)
      change
        P[(fun η => α (k + 1) * w (u (k + 1) η)) | 𝓖 k] =ᵐ[P]
          (fun ω => α (k + 1) *
            (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω) at hs
      exact hs
    filter_upwards [hstep k, hce] with ω hk hc
    calc
      α k * a k ω +
          (P[(fun η => α (k + 1) * w (u (k + 1) η)) | 𝓖 k]) ω =
        α k * a k ω +
          α (k + 1) * (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω := by rw [hc]
      _ = α k * (a k ω + β k *
          (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω) := by
        rw [hfactor k]
        ring
      _ ≤ α k * w (u k ω) := mul_le_mul_of_nonneg_left hk (hα k)
  exact AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_steps
    P 𝓖
    (fun k ω => α k * a k ω)
    (fun k ω => α k * w (u k ω))
    hCashI hVI hscaled n
