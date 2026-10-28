-- Prove2me | solution 1 for AvramDividend.Classical.exponential_levy_grid_cash_stieltjes_limit_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:31:51.128761+00:00
-- url     : https://prove2.me/submissions/5ac3fbe8-fecd-41cc-a6d1-0ab143abe560

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_expected_cash_le_initial_of_conditional_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A monotone Stieltjes payout dominated by discounted grid cash inherits
    the conditional stochastic-verification upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable
      (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
          Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (hterminal : ∀ n : ℕ, 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P)
    (hPrefixI : ∀ n : ℕ, Integrable
      (fun ω => ∑ k ∈ Finset.range n, cash k ω) P)
    (hPrefixNN : ∀ n : ℕ, 0 ≤ᵐ[P]
      (fun ω => ∑ k ∈ Finset.range n, cash k ω))
    (hPrefixAE : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω)) P)
    (hMono : ∀ᵐ ω ∂P, Monotone
      (fun n : ℕ => ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k ω)))
    (Z : Ω → ENNReal)
    (hZ : ∀ᵐ ω ∂P, Z ω ≤
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k ω)) :
    (∫⁻ ω, Z ω ∂P) ≤ ENNReal.ofReal (w x) := by
  have hgrid : ∀ n : ℕ,
      (∫⁻ ω, ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    have hbudget :=
      AvramDividend.Classical.exponential_levy_grid_expected_cash_le_initial_of_conditional_cash
        P 𝓕 s hs hs0 u cash w q x
        hu0 hCashI hVI hstep n (hterminal n)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hPrefixI n) (hPrefixNN n)]
    rw [MeasureTheory.integral_finsetSum (Finset.range n)
      (by intro k hk; exact hCashI k)]
    exact ENNReal.ofReal_le_ofReal hbudget
  calc
    (∫⁻ ω, Z ω ∂P) ≤
        ∫⁻ ω, (⨆ n : ℕ,
          ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω)) ∂P :=
      MeasureTheory.lintegral_mono_ae hZ
    _ = ⨆ n : ℕ, ∫⁻ ω,
        ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω) ∂P :=
      MeasureTheory.lintegral_iSup' hPrefixAE hMono
    _ ≤ ENNReal.ofReal (w x) := iSup_le hgrid
