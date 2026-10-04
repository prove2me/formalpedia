-- Prove2me | solution 1 for BJNAdAuctions.Basic.competitive_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:48:09.325309+00:00
-- url     : https://prove2.me/submissions/3fc08f6c-34f1-4f7a-a410-1636be23e1a7

import Mathlib

open Filter Topology in
theorem solution :
    Tendsto (fun R : ℝ => (1 - 1 / (1 + R) ^ (1 / R)) * (1 - R)) (𝓝[>] 0)
      (𝓝 (1 - Real.exp (-1))) := by
  have hinv : Tendsto (fun R : ℝ => 1 / R) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h0 := (Real.tendsto_one_add_div_rpow_exp 1).comp hinv
  have h1 : Tendsto (fun R : ℝ => (1 + R) ^ (1 / R)) (𝓝[>] (0:ℝ)) (𝓝 (Real.exp 1)) := by
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with R hR
    simp only [Function.comp_apply, one_div_one_div]
  have h2 : Tendsto (fun R : ℝ => 1 - R) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have : Tendsto (fun R : ℝ => 1 - R) (𝓝 (0:ℝ)) (𝓝 (1 - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun R : ℝ => (1 - 1 / (1 + R) ^ (1 / R)) * (1 - R)) (𝓝[>] (0:ℝ))
      (𝓝 ((1 - 1 / Real.exp 1) * 1)) :=
    ((tendsto_const_nhds.sub (tendsto_const_nhds.div h1 (Real.exp_pos 1).ne')).mul h2)
  rw [mul_one, one_div, ← Real.exp_neg] at h3
  exact h3
