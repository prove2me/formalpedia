-- Prove2me | solution 1 for AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_steps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:27:35.769901+00:00
-- url     : https://prove2.me/submissions/530b532b-a5e0-4b6f-8e37-ed76c6a485ac

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (cash V : ℕ → Ω → ℝ)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable (V k) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      cash k ω + (P[(V (k + 1)) | 𝓖 k]) ω ≤ V k ω)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) +
        ∫ ω, V n ω ∂P ≤
      ∫ ω, V 0 ω ∂P := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hCE : Integrable (P[(V (n + 1)) | 𝓖 n]) P :=
        integrable_condExp
      have hstepI :
          (∫ ω, cash n ω ∂P) + (∫ ω, V (n + 1) ω ∂P) ≤
            ∫ ω, V n ω ∂P := by
        have h := integral_mono_ae
          ((hCashI n).add hCE) (hVI n) (hstep n)
        simp only [Pi.add_apply] at h
        rw [integral_add (hCashI n) hCE,
          integral_condExp (𝓖.le n)] at h
        exact h
      rw [Finset.sum_range_succ]
      linarith
