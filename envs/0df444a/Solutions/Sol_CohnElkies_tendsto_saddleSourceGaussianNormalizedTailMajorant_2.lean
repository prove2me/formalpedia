-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSourceGaussianNormalizedTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:56.525467+00:00
-- url     : https://prove2.me/submissions/560b6b05-4bef-4dcb-8f53-f3d0b67282b7

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


theorem solution :
    Tendsto saddleSourceGaussianNormalizedTailMajorant
      atTop (𝓝 (0 : ℝ)) := by
  unfold saddleSourceGaussianNormalizedTailMajorant
  have h1 : Tendsto (fun x : ℝ => -(x ^ (1 / 6 : ℝ)) / 8) atTop atBot := by
    have := (tendsto_rpow_atTop (show (0:ℝ) < 1/6 by norm_num)).atTop_div_const (show (0:ℝ) < 8 by norm_num)
    have := Filter.tendsto_neg_atTop_atBot.comp this
    refine this.congr fun x => ?_
    simp [neg_div]
  have := (Real.tendsto_exp_atBot.comp h1).const_mul (4 * Real.sqrt (2 * Real.pi))
  simpa using this

