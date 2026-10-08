-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_open_interval_of_compact_subintervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:30:47.562464+00:00
-- url     : https://prove2.me/submissions/26866f4f-ed31-4a8c-b24f-a3c5dcbc5387

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hK : ∀ (l u : ℝ), 0 < l → l < u → u < a →
      ContinuousOn f (Icc l u)) :
    ContinuousOn f (Ioo 0 a) := by
  intro x hx
  let l : ℝ := x / 2
  let u : ℝ := (x + a) / 2
  have hl : 0 < l := by dsimp [l]; linarith [hx.1]
  have hxl : l < x := by dsimp [l]; linarith [hx.1]
  have hxu : x < u := by dsimp [u]; linarith [hx.2]
  have hu : u < a := by dsimp [u]; linarith [hx.2]
  have hlu : l < u := lt_trans hxl hxu
  have hcont : ContinuousOn f (Icc l u) :=
    hK l u hl hlu hu
  have hnhds : Icc l u ∈ 𝓝 x := by
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hxl, hxu⟩)
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  exact (hcont.continuousAt hnhds).continuousWithinAt
