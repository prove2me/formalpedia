-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_arrival_sum_future_suffix_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T17:56:49.304268+00:00
-- url     : https://prove2.me/submissions/093a1961-7ac7-46a0-adb7-4f595f03085d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Split the arrival at index n+m into the arrival at n and
the following m waiting times. -/
theorem solution (τ : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range ((n + 1) + m), τ i) =
      (∑ i ∈ Finset.range (n + 1), τ i) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) := by
  exact Finset.sum_range_add τ (n + 1) m
