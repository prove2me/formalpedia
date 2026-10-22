-- Prove2me | solution 1 for DemandSubstitution.Comparison.eq1_profit_underage_overage
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:33:26.755538+00:00
-- url     : https://prove2.me/submissions/330536bf-e537-4793-a7d1-b84c4a830b82

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

set_option autoImplicit false
open MeasureTheory DemandSubstitution.Comparison

theorem solution {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    (Q : Fin n → ℝ) :
    centralProfit M μ Q =
      ∫ x, ∑ i, (M.u i * Ds M Q x i - M.u i * max (Ds M Q x i - Q i) 0
        - M.o i * max (Q i - Ds M Q x i) 0) ∂μ := by
  unfold centralProfit
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Model.u, Model.o]
  rcases le_total (Ds M Q x i) (Q i) with h | h
  · have h1 : max (Ds M Q x i - Q i) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (Q i - Ds M Q x i) 0 = Q i - Ds M Q x i := max_eq_left (by linarith)
    rw [min_eq_left h, h1, h2]
    ring
  · have h1 : max (Ds M Q x i - Q i) 0 = Ds M Q x i - Q i := max_eq_left (by linarith)
    have h2 : max (Q i - Ds M Q x i) 0 = 0 := max_eq_right (by linarith)
    rw [min_eq_right h, h1, h2]
    ring
