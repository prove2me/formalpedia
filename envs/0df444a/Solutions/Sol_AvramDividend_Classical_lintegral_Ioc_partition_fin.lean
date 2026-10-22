-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_Ioc_partition_fin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:26:03.978112+00:00
-- url     : https://prove2.me/submissions/be6162dd-c7c2-46f9-9a96-a3d69707fdb1

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

/-- Finite-grid additivity of nonnegative Stieltjes payments on adjacent
half-open time cells, including possibly infinite total mass. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∫⁻ r in Set.Ioc (u 0) (u n), f r ∂μ) =
    ∑ i ∈ Finset.range n,
      ∫⁻ r in Set.Ioc (u i) (u (i + 1)), f r ∂μ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h0n : u 0 ≤ u n := hu (Nat.zero_le n)
      have hn : u n ≤ u (n + 1) := hu (Nat.le_succ n)
      calc
        (∫⁻ r in Set.Ioc (u 0) (u (n + 1)), f r ∂μ) =
            (∫⁻ r in Set.Ioc (u 0) (u n), f r ∂μ) +
            (∫⁻ r in Set.Ioc (u n) (u (n + 1)), f r ∂μ) :=
          lintegral_Ioc_adjacent_add μ f (u 0) (u n) (u (n + 1)) h0n hn
        _ = (∑ i ∈ Finset.range n,
               ∫⁻ r in Set.Ioc (u i) (u (i + 1)), f r ∂μ) +
            (∫⁻ r in Set.Ioc (u n) (u (n + 1)), f r ∂μ) := by
              rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1),
              ∫⁻ r in Set.Ioc (u i) (u (i + 1)), f r ∂μ := by
              rw [Finset.sum_range_succ]
