-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_count_increment_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:26:26.845335+00:00
-- url     : https://prove2.me/submissions/621e97b3-2906-4cc8-8e4f-55fc84ad8138

import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Shift a threshold-count equivalence by the observed count at the earlier time. -/
theorem solution
    {Ω : Type*}
    (τ : ℕ → Ω → ℝ)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (ω : Ω) (u v : ℝ) (k : ℕ) :
    k < N ω v - N ω u ↔
      (∑ i ∈ Finset.range (N ω u + k + 1), τ i ω) ≤ v := by
  constructor
  · intro h
    apply (hThreshold ω v (N ω u + k)).mp
    omega
  · intro h
    have hcount : N ω u + k < N ω v :=
      (hThreshold ω v (N ω u + k)).mpr h
    omega
