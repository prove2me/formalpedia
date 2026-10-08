-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_Ioo_of_continuousOn_all_compact_subintervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:55:24.599095+00:00
-- url     : https://prove2.me/submissions/3fde4db6-25d8-409a-b347-765e2bfd83c6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
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
  have hnhds : Icc l u ∈ 𝓝 x := by
    apply Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hxl, hxu⟩)
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  exact ((hcompact l u hl hlu hu).continuousAt hnhds).continuousWithinAt
