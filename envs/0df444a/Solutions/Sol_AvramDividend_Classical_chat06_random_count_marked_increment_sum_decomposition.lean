-- Prove2me | solution 1 for AvramDividend.Classical.chat06_random_count_marked_increment_sum_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:49:38.261096+00:00
-- url     : https://prove2.me/submissions/e77bc89e-3944-4efe-a9e9-0c86e22f573e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- A compound Poisson mark-sum increment between two observations
is precisely the sum of marks indexed after the earlier count,
provided the event count is nondecreasing. -/
theorem solution
    {Ω : Type*}
    (Y : ℕ → Ω → ℝ)
    (Ns Nt : Ω → ℕ) (hmono : ∀ ω, Ns ω ≤ Nt ω)
    (ω : Ω) :
    (∑ i ∈ Finset.range (Nt ω), Y i ω) -
      (∑ i ∈ Finset.range (Ns ω), Y i ω) =
      ∑ j ∈ Finset.range (Nt ω - Ns ω), Y (Ns ω + j) ω := by
  have hIndex : Ns ω + (Nt ω - Ns ω) = Nt ω :=
    Nat.add_sub_of_le (hmono ω)
  rw [← hIndex, Finset.sum_range_add]
  simp
