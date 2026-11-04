-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:28:51.149163+00:00
-- url     : https://prove2.me/submissions/490c0d6d-1ef8-4647-a3c2-9112234a65df

import Mathlib
-- Preserve the full import: auto targeted imports omitted Filter, Tendsto and ℝ (CE 24784).

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- Continuous tests commute with finite sums of convergent selected jump-grid increments. -/
theorem solution
    {α : Type*} (s : Finset α)
    (a : α → ℕ → ℝ) (b : α → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (h : ∀ u ∈ s, Tendsto (a u) atTop (𝓝 (b u))) :
    Tendsto (fun n : ℕ => ∑ u ∈ s, f (a u n))
      atTop (𝓝 (∑ u ∈ s, f (b u))) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  | @insert u s hus ih =>
      intro h
      have hu : Tendsto (a u) atTop (𝓝 (b u)) :=
        h u (Finset.mem_insert_self u s)
      have hs : ∀ v ∈ s, Tendsto (a v) atTop (𝓝 (b v)) := by
        intro v hv
        exact h v (Finset.mem_insert_of_mem hv)
      have hfu : Tendsto (fun n : ℕ => f (a u n))
          atTop (𝓝 (f (b u))) :=
        (hf.continuousAt.tendsto.comp hu)
      simpa only [Finset.sum_insert hus] using hfu.add (ih hs)
