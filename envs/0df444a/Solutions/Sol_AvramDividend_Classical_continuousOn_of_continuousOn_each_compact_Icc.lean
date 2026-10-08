-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_of_continuousOn_each_compact_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:04:01.349642+00:00
-- url     : https://prove2.me/submissions/3a1a076d-54ca-43d4-abd9-d78abe4b7891

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f : ℝ → ℝ) (a : ℝ)
    (hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
      ContinuousOn f (Icc l u)) :
    ContinuousOn f (Ioo 0 a) := by
  intro x hx
  let l : ℝ := x / 2
  let u : ℝ := (x + a) / 2
  have hl : 0 < l := by dsimp [l]; linarith [hx.1]
  have hlu : l < u := by dsimp [l, u]; linarith [hx.1, hx.2]
  have hu : u < a := by dsimp [u]; linarith [hx.2]
  have hxl : l < x := by dsimp [l]; linarith [hx.1]
  have hxu : x < u := by dsimp [u]; linarith [hx.2]
  have hxIcc : x ∈ Icc l u := ⟨le_of_lt hxl, le_of_lt hxu⟩
  have hnhds : Icc l u ∈ 𝓝 x := by
    apply Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds (show x ∈ Ioo l u from ⟨hxl, hxu⟩))
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  exact ((hcompact l u hl hlu hu) x hxIcc).continuousAt hnhds |>.continuousWithinAt
