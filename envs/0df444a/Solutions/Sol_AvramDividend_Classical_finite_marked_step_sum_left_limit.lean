-- Prove2me | solution 1 for AvramDividend.Classical.finite_marked_step_sum_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:09:49.055318+00:00
-- url     : https://prove2.me/submissions/a8f66421-cc53-4259-9b91-eb8259fc8e30

import Mathlib

open Filter Set Topology
open scoped NNReal BigOperators
theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    Tendsto
      (fun s : ℝ≥0 => ∑ i ∈ S, if τ i ≤ s then w i else 0)
      (nhdsWithin t (Iio t))
      (nhds (∑ i ∈ S, if τ i < t then w i else 0)) := by
  have key : ∀ᶠ s in 𝓝[<] t, ∀ i ∈ S, (τ i ≤ s ↔ τ i < t) := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases h : τ i < t
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds h)] with s hs
      simp only [h, iff_true]
      exact le_of_lt hs
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [h, iff_false, not_le]
      exact lt_of_lt_of_le hs (not_lt.mp h)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [key] with s hs
  exact Finset.sum_congr rfl fun i hi => by simp only [hs i hi]
