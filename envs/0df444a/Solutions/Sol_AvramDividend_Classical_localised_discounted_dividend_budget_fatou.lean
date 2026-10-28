-- Prove2me | solution 1 for AvramDividend.Classical.localised_discounted_dividend_budget_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:22:05.806264+00:00
-- url     : https://prove2.me/submissions/231fad1e-79b3-4fe9-b6e4-540d158dd9a7

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-! Remove localisation of expected dividend budgets by Fatou's lemma. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → ENNReal) (B : Ω → ENNReal) (budget : ENNReal)
    (hAmeas : ∀ n, Measurable (A n))
    (hLimit : ∀ ω, B ω ≤ Filter.liminf (fun n : ℕ => A n ω) Filter.atTop)
    (hBound : ∀ n, (∫⁻ ω, A n ω ∂P) ≤ budget) :
    (∫⁻ ω, B ω ∂P) ≤ budget := by
  calc
    (∫⁻ ω, B ω ∂P) ≤
        (∫⁻ ω, Filter.liminf (fun n : ℕ => A n ω) Filter.atTop ∂P) := by
      exact lintegral_mono hLimit
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω, A n ω ∂P) Filter.atTop := by
      exact lintegral_liminf_le hAmeas
    _ ≤ budget := by
      calc
        Filter.liminf (fun n : ℕ => ∫⁻ ω, A n ω ∂P) Filter.atTop ≤
            Filter.liminf (fun _ : ℕ => budget) Filter.atTop := by
          exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hBound)
        _ = budget := by simp
