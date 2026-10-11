-- Prove2me | solution 1 for FredholmBanach.isCompactOperator_of_finiteDimensional_range
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:37:37.953297+00:00
-- url     : https://prove2.me/submissions/734e60ff-9344-4eab-8df1-7eeaf8f4db25

import Definitions.Def_FredholmBanach_Setting
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : E →L[𝕜] F) (hh : FiniteDimensional 𝕜 h.range) :
    IsCompactOperator h := by
  haveI : ProperSpace h.range := FiniteDimensional.proper_rclike 𝕜 h.range
  refine ⟨Subtype.val '' Metric.closedBall (0 : h.range) ‖h‖,
    (isCompact_closedBall _ _).image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) one_pos) fun x hx => ?_
  refine ⟨⟨h x, LinearMap.mem_range_self _ x⟩, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm]
  rw [Metric.mem_ball, dist_zero_right] at hx
  calc ‖h x‖ ≤ ‖h‖ * ‖x‖ := h.le_opNorm x
    _ ≤ ‖h‖ * 1 := by gcongr
    _ = ‖h‖ := mul_one _
