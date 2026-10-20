-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusVariable_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:05.395545+00:00
-- url     : https://prove2.me/submissions/de3f5d10-4623-4e14-a490-9809a79cc9ce

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε : ℝ} {d : ℕ} (hd : 0 < d) :
    saddleSmallRadiusVariable ε (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma
            (Real.log ((d : ℝ) / 2) / 8) +
          2 *
            (saddleShellDerivativeOne ε +
              saddleSourceShellDerivative ε
                (saddleSmallRadiusStarOrdinate ε d))) := by
  have hd' : (0:ℝ) < (d:ℝ)/2 := by positivity
  have harg : ((d:ℝ)/2) * (1 + saddleSmallRadiusStarOrdinate ε d) / 2 = Real.log ((d:ℝ)/2) / 8 := by
    show ((d:ℝ)/2) * (1 + (-1 + Real.log ((d:ℝ)/2) / (4 * ((d:ℝ)/2)))) / 2 = _
    field_simp
    ring
  unfold saddleSmallRadiusVariable saddleSmallRadiusStar saddleLogRadius saddleSourceShellDerivative
  rw [harg, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  rw [← Real.exp_log Real.pi_pos, ← Real.exp_add, Real.log_exp]
  congr 1
  push_cast
  ring

