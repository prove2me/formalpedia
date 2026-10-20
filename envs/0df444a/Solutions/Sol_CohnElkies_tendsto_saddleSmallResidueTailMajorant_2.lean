-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSmallResidueTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:19.032323+00:00
-- url     : https://prove2.me/submissions/e4e9bac7-e070-42f5-be55-7f482c8ac3fb

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
    (C : ℝ) :
    Tendsto (saddleSmallResidueTailMajorant C)
      atTop (𝓝 0) := by
  unfold saddleSmallResidueTailMajorant
  have h1 : Tendsto (fun ℓ : ℝ => -((77 / 8 : ℝ) * Real.log ℓ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
  have h2 := Filter.tendsto_atBot_add_const_left atTop (3 * C) h1
  exact Real.tendsto_exp_atBot.comp (h2.congr fun ℓ => by ring)

