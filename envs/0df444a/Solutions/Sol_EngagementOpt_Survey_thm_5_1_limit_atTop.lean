-- Prove2me | solution 1 for EngagementOpt.Survey.thm_5_1_limit_atTop
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:38:03.337609+00:00
-- url     : https://prove2.me/submissions/3e0cd151-f0be-4608-83ad-91c5565a506b

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

set_option autoImplicit false
open Filter Topology EngagementOpt.Survey

theorem solution : Tendsto phi atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add
      ((tendsto_const_nhds (x := (1:ℝ))).div_atTop (tendsto_id (α := ℝ)))
  have hl : (fun x : ℝ => Real.log (x + 1)) =o[atTop] (fun x : ℝ => x + 1) :=
    Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hl' : Tendsto (fun x : ℝ => Real.log (x + 1) / (x + 1)) atTop (𝓝 0) :=
    hl.tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log (x + 1) / (x + 1) * (1 + 1 / x)) atTop (𝓝 0) := by
    simpa using hl'.mul h1
  have h3 : Tendsto (fun x : ℝ => (1 + 1 / x) * (1 - Real.log (x + 1) / (x + 1) * (1 + 1 / x)))
      atTop (𝓝 1) := by
    simpa using h1.mul (tendsto_const_nhds.sub h2)
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx1 : x + 1 ≠ 0 := by linarith
  simp only [phi]
  field_simp
