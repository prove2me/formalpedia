-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_renewal_tsum_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:40:35.126378+00:00
-- url     : https://prove2.me/submissions/f4fa982c-d810-4302-8249-a9fc16f73dd6

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Field

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Topology
open scoped BigOperators

/-- The singleton partial sum is bounded by every nonnegative convergent renewal series. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℝ → ℕ → ℝ)
    (hκ : Tendsto κ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop)
    (hsum : ∀ x : ℝ, 0 < x → Summable (F x))
    (hfirst : ∀ x : ℝ, 0 < x → F x 0 = κ x)
    (hnonneg : ∀ x : ℝ, 0 < x → ∀ n : ℕ, 0 ≤ F x n) :
    Tendsto (fun x : ℝ => ∑' n : ℕ, F x n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
  rw [Filter.tendsto_atTop] at hκ ⊢
  intro b
  filter_upwards [hκ b, self_mem_nhdsWithin] with x hbx hx
  have hxpos : 0 < x := hx
  have hle : F x 0 ≤ ∑' n : ℕ, F x n := by
    have hsum_le := sum_le_hasSum ({0} : Finset ℕ)
      (by intro n hn; exact hnonneg x hxpos n)
      (hsum x hxpos).hasSum
    simpa using hsum_le
  rw [← hfirst x hxpos] at hbx
  exact hbx.trans hle
