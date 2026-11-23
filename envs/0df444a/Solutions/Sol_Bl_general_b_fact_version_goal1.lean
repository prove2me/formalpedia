-- Prove2me | solution 1 for Bl.general_b_fact_version.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:12.786786+00:00
-- url     : https://prove2.me/submissions/0eb2869b-bb4b-4c8a-91cf-e8aae3c2cf50

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_version
namespace Bl.general_b_fact_version
theorem _root_.solution :
  ∀ {Y : Type u_1} [inst : NormedAddCommGroup.{u_1} Y] [inst_1 : NormedSpace.{0, u_1} Complex Y] {g : Y → Complex} {y : Y}
  {R M : Real},
  LT.lt.{0} 0 R →
    DifferentiableOn.{0, u_1, 0} Complex g (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) →
      (∀ (v : Y),
          Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) v →
            LE.le.{0} (Norm.norm.{0} (g v)) M) →
        LE.le.{0} (Norm.norm.{u_1} (fderiv.{0, u_1, 0} Complex g y)) (HDiv.hDiv.{0, 0, 0} M R) := by
  intro Y _ _ g y R M hR hd hM
  have hy : y ∈ Metric.ball y (2 * R) := Metric.mem_ball_self (by positivity)
  have hmaps : Set.MapsTo g (Metric.ball y (2 * R)) (Metric.closedBall (g y) (2 * M)) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖g v - g y‖ ≤ ‖g v‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM v hv) (hM y hy)
      _ = 2 * M := by ring
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hmaps (by positivity)
  calc ‖fderiv ℂ g y‖ ≤ 2 * M / (2 * R) := h
    _ = M / R := by rw [mul_div_mul_left _ _ (two_ne_zero)]
end Bl.general_b_fact_version
