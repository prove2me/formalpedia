-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_stopped_prefix_eq_masked_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:00:13.428339+00:00
-- url     : https://prove2.me/submissions/b57c2818-60fa-427e-8b14-c265043d50b0

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped BigOperators

/-- A bounded, randomly stopped prefix is exactly the masked deterministic
finite envelope, including its final contact cell. -/
theorem solution (N k : ℕ) (hk : k ≤ N) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, if i < k then f i else 0) =
      ∑ i ∈ Finset.range k, f i := by
  have hfilter : (Finset.range N).filter (fun i => i < k) =
      Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    (∑ i ∈ Finset.range N, if i < k then f i else 0) =
        ∑ i ∈ (Finset.range N).filter (fun i => i < k), f i := by
      simp only [Finset.sum_filter]
    _ = ∑ i ∈ Finset.range k, f i := by rw [hfilter]
