-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_sinf_count_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:26:58.640642+00:00
-- url     : https://prove2.me/submissions/f5787203-f21d-4793-b513-5b65752c25be

import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- For a nondecreasing divergent arrival sequence, the renewal
count defined as the first strictly future arrival index exceeds k
exactly when the kth indexed arrival has already occurred. -/
theorem solution
    (arrival : ℕ → ℝ) (t : ℝ)
    (hmono : Monotone arrival)
    (hne : ∃ n : ℕ, t < arrival n)
    (k : ℕ) :
    k < sInf {n : ℕ | t < arrival n} ↔ arrival k ≤ t := by
  have hnonempty : ({n : ℕ | t < arrival n} : Set ℕ).Nonempty :=
    hne
  have hLe :
      sInf {n : ℕ | t < arrival n} ≤ k ↔
        t < arrival k := by
    constructor
    · intro h
      exact lt_of_lt_of_le (Nat.sInf_mem hnonempty) (hmono h)
    · intro h
      exact Nat.sInf_le h
  constructor
  · intro hk
    by_contra hbad
    have hgt : t < arrival k := lt_of_not_ge hbad
    exact (not_le_of_gt hk) (hLe.mpr hgt)
  · intro hk
    by_contra hbad
    have hle : sInf {n : ℕ | t < arrival n} ≤ k :=
      le_of_not_gt hbad
    exact (not_lt_of_ge hk) (hLe.mp hle)
