-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_uniform_geometric_moment_bound_forces_zero_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:17.823986+00:00
-- url     : https://prove2.me/submissions/dca80f36-e692-41c4-a14c-3e48d691c427

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (R m M : ℝ) (hR : 1 < R) (hm : 0 ≤ m)
    (hbound : ∀ n : ℕ, R ^ n * m ≤ M) :
    m = 0 := by
  by_contra hne
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hne)
  obtain ⟨n, hpow⟩ : ∃ n : ℕ, M / m < R ^ n :=
    pow_unbounded_of_one_lt (M / m) hR
  have hstrict : M < R ^ n * m :=
    (div_lt_iff₀ hmpos).mp hpow
  exact (not_le_of_gt hstrict) (hbound n)
