-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_count_monotone_from_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:03:44.360292+00:00
-- url     : https://prove2.me/submissions/fbca3c65-8887-4d70-83fd-f9def580a0ce

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The exact arrival-time threshold characterisation makes the
renewal counting process nondecreasing in observation time. -/
theorem solution
    {Ω : Type*}
    (τ : ℕ → Ω → ℝ)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (ω : Ω) (u v : ℝ) (huv : u ≤ v) :
    N ω u ≤ N ω v := by
  by_contra h
  have hlt : N ω v < N ω u := Nat.lt_of_not_ge h
  have hArrival :
      (∑ i ∈ Finset.range (N ω v + 1), τ i ω) ≤ u :=
    (hThreshold ω u (N ω v)).mp hlt
  have hSelf : N ω v < N ω v :=
    (hThreshold ω v (N ω v)).mpr (hArrival.trans huv)
  exact (lt_irrefl _) hSelf
