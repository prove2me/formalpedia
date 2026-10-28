-- Prove2me | solution 1 for AvramDividend.Classical.uniform_upper_bound_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:19:17.989369+00:00
-- url     : https://prove2.me/submissions/33b6a240-1484-4f87-b5c9-5ed4d5dbbb8b

import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

/-- A constant dominated by a sequence converging to zero cannot be positive. -/
theorem solution
    (A : ℝ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds (0 : ℝ)))
    (hBound : ∀ n : ℕ, A ≤ b n) :
    A ≤ 0 := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hb
    (Filter.Eventually.of_forall hBound)
