-- Prove2me | solution 2 for CohnElkies.stripNormalizedPoissonExtension_continuousAt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:16:33.683478+00:00
-- url     : https://prove2.me/submissions/b9805bab-cb33-4e9b-adc2-8abce6deda79

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution (T : ℝ) :
    ContinuousAt (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
      1 := by
  unfold stripNormalizedPoissonExtension
  have hs : Continuous fun σ : ℝ => Real.sinc (Real.pi * (1 - σ) / 2) := Real.continuous_sinc.comp (by fun_prop)
  apply ContinuousAt.div (continuous_const.mul hs).continuousAt (by fun_prop)
  rw [show Real.pi * (1 - 1) / 2 = 0 by ring, Real.cos_zero]
  apply ne_of_gt
  linarith [Real.cosh_pos (Real.pi * T / 2)]

