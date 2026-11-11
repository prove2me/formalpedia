-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18f_finite_marked_step_sum_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:16:18.046204+00:00
-- url     : https://prove2.me/submissions/f82216de-0b79-4f54-a2e5-9655007db3a6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- A finite marked jump path with the right-closed arrival convention is
right-continuous at every finite time. -/
theorem solution
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => ∑ i ∈ S, if τ i ≤ s then w i else 0)
      (Ici t) t := by
  classical
  change Tendsto
    (fun s : ℝ≥0 => ∑ i ∈ S, if τ i ≤ s then w i else 0)
    (𝓝[Ici t] t)
    (𝓝 (∑ i ∈ S, if τ i ≤ t then w i else 0))
  apply tendsto_finset_sum S
  intro i hi
  by_cases h : τ i ≤ t
  · have hev : ∀ᶠ s : ℝ≥0 in 𝓝[Ici t] t, τ i ≤ s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact h.trans hs
    have heq :
        (fun s : ℝ≥0 => if τ i ≤ s then w i else 0) =ᶠ[𝓝[Ici t] t]
          (fun _ => w i) := by
      filter_upwards [hev] with s hs
      simp [hs]
    simpa [h] using (tendsto_const_nhds.congr' heq.symm)
  · have ht : t < τ i := lt_of_not_ge h
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝[Ici t] t, s < τ i :=
      (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
    have heq :
        (fun s : ℝ≥0 => if τ i ≤ s then w i else 0) =ᶠ[𝓝[Ici t] t]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [hev] with s hs
      simp [not_le.mpr hs]
    simpa [h] using (tendsto_const_nhds.congr' heq.symm)
