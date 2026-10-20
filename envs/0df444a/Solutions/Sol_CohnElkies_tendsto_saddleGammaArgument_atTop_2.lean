-- Prove2me | solution 2 for CohnElkies.tendsto_saddleGammaArgument_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:30.150976+00:00
-- url     : https://prove2.me/submissions/bce9cae4-d34e-42e2-a4d0-620e9f8a6a59

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {d : ℕ} (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        ((d : ℝ) / 2) * (1 + u) / 2)
      atTop atTop := by
  have hd' : (0:ℝ) < (d : ℝ) / 2 := by positivity
  exact ((Filter.tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hd').atTop_div_const (by norm_num)

