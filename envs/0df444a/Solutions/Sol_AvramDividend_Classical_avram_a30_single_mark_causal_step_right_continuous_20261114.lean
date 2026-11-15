-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_single_mark_causal_step_right_continuous_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:27:04.221896+00:00
-- url     : https://prove2.me/submissions/06f6cbc8-3bc7-4c0f-bce1-2af3ad56a27e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- A real step contribution of a marked jump is right-continuous at every time. -/
theorem solution (u : ℝ≥0) (a : ℝ) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => if u ≤ v then a else 0)
        (Ici t) t := by
  intro t
  by_cases hut : u ≤ t
  · have he : (fun v : ℝ≥0 => if u ≤ v then a else 0) =ᶠ[𝓝[Ici t] t]
        (fun _ => a) := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp [le_trans hut hv]
    change Tendsto (fun v : ℝ≥0 => if u ≤ v then a else 0)
      (𝓝[Ici t] t) (𝓝 (if u ≤ t then a else 0))
    rw [if_pos hut]
    exact tendsto_const_nhds.congr' he.symm
  · have htu : t < u := lt_of_not_ge hut
    have he : (fun v : ℝ≥0 => if u ≤ v then a else 0) =ᶠ[𝓝[Ici t] t]
        (fun _ => (0 : ℝ)) := by
      have he' : ∀ᶠ v : ℝ≥0 in 𝓝[Ici t] t, v < u :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds htu)
      filter_upwards [he'] with v hv
      simp [not_le.mpr hv]
    change Tendsto (fun v : ℝ≥0 => if u ≤ v then a else 0)
      (𝓝[Ici t] t) (𝓝 (if u ≤ t then a else 0))
    rw [if_neg hut]
    exact tendsto_const_nhds.congr' he.symm
