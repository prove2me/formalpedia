-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:26:49.142306+00:00
-- url     : https://prove2.me/submissions/a7ed980a-fcdc-4f3d-88a6-9dcb6eb19209

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Actual càdlàg jump marks vanish strictly to the right of every fixed
time, including the initial time, by right continuity and left limits. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => Y u - Function.leftLim Y u)
      (𝓝[>] t) (𝓝 (0 : ℝ)) := by
  let g : ℝ≥0 → ℝ := Function.leftLim Y
  have hright : Tendsto Y (𝓝[>] t) (𝓝 (Y t)) :=
    (hR t).mono_left (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r : ℝ := ε / 3
  have hr : 0 < r := by dsimp [r]; linarith
  have hev : ∀ᶠ u in 𝓝[>] t, dist (Y u) (Y t) < r := by
    exact hright.eventually (Metric.ball_mem_nhds (Y t) hr)
  obtain ⟨b, hb, hcover⟩ := (nhdsGT_basis t).mem_iff.mp hev
  apply (nhdsGT_basis t).mem_iff.mpr
  refine ⟨b, hb, ?_⟩
  intro u hu
  have hu_pos : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) hu.1
  have hleft : Tendsto Y (𝓝[<] u) (𝓝 (g u)) := hL u hu_pos
  haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨t, hu.1⟩
  have hnear :
      ∀ᶠ v in 𝓝[<] u, Y v ∈ Metric.closedBall (Y t) r := by
    filter_upwards [Ioo_mem_nhdsLT hu.1] with v hv
    apply Metric.mem_closedBall.mpr
    exact le_of_lt (hcover ⟨hv.1, lt_trans hv.2 hu.2⟩)
  have hgu : dist (g u) (Y t) ≤ r :=
    Metric.mem_closedBall.mp
      (Metric.isClosed_closedBall.mem_of_tendsto hleft hnear)
  have hfu : dist (Y u) (Y t) < r := hcover hu
  have htri : dist (Y u) (g u) ≤ dist (Y u) (Y t) + dist (Y t) (g u) :=
    dist_triangle _ _ _
  have htwo : dist (Y u) (g u) < r + r := by
    calc
      dist (Y u) (g u) ≤ dist (Y u) (Y t) + dist (Y t) (g u) := htri
      _ < r + r := add_lt_add_of_lt_of_le hfu (by simpa [dist_comm] using hgu)
  have hsmall : r + r < ε := by dsimp [r]; linarith
  change dist (Y u - g u) 0 < ε
  simpa [Real.dist_eq] using lt_trans htwo hsmall
