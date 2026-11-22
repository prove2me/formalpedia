-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_cont_pick_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:25:00.589868+00:00
-- url     : https://prove2.me/submissions/7c6a6920-4c28-4b0a-8f10-659cab651b35

import Mathlib.Topology.MetricSpace.Pseudo.Defs
open Filter Set Topology
noncomputable section
set_option autoImplicit false

theorem solution (W : ℝ → ℝ) (c : ℝ)
    (hCont : ContinuousOn W (Ici (0:ℝ))) (hW0 : W 0 = 0) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ W a < c := by
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hContAt : ContinuousWithinAt W (Ici (0 : ℝ)) 0 := hCont 0 h0mem
  rw [Metric.continuousWithinAt_iff] at hContAt
  obtain ⟨δ, hδpos, hδ⟩ := hContAt c hc
  have ha_pos : 0 < δ / 2 := by linarith
  have ha_mem : δ / 2 ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_of_lt ha_pos)
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq]
    have habs : |δ / 2 - 0| = δ / 2 := by
      rw [sub_zero]
      exact abs_of_pos ha_pos
    rw [habs]
    linarith
  have hWdist : dist (W (δ / 2)) (W 0) < c := hδ (x := δ / 2) ha_mem hdist
  rw [hW0] at hWdist
  rw [Real.dist_eq] at hWdist
  have hlt : W (δ / 2) - 0 < c := lt_of_le_of_lt (le_abs_self _) hWdist
  have hWlt : W (δ / 2) < c := by linarith
  exact ⟨δ / 2, ha_pos, hWlt⟩
