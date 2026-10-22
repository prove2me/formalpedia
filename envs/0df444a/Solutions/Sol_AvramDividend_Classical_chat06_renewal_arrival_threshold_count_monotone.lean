-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_arrival_threshold_count_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T17:56:25.080745+00:00
-- url     : https://prove2.me/submissions/198829a3-9139-460b-8868-ac1dcd984be7

import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact arrival-threshold counts cannot decrease as observation time
increases: any arrival already counted at s remains counted at t ≥ s. -/
theorem solution
    (arrival : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ t k, k < N t ↔ arrival k ≤ t) :
    Monotone N := by
  intro s t hst
  by_contra hbad
  have hgt : N t < N s := Nat.lt_of_not_ge hbad
  have hArr : arrival (N t) ≤ s :=
    (hThreshold s (N t)).mp hgt
  have hlt : N t < N t :=
    (hThreshold t (N t)).mpr (le_trans hArr hst)
  exact Nat.lt_irrefl (N t) hlt
