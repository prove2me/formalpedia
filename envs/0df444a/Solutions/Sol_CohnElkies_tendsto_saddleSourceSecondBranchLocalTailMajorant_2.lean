-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSourceSecondBranchLocalTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:36.639637+00:00
-- url     : https://prove2.me/submissions/90479d0b-bf50-415b-8fac-76542587f16f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution :
    Tendsto
      (fun ℓ : ℝ =>
        2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
          Real.exp
            (-(ℓ ^ (1 / 6 : ℝ) /
              (400 * Real.exp 1))))
      atTop (𝓝 (0 : ℝ)) := by
  have h1 : Tendsto (fun ℓ : ℝ => ℓ ^ (1/6:ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h2 : Tendsto (fun ℓ : ℝ => -(ℓ ^ (1/6:ℝ) / (400 * Real.exp 1))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (h1.atTop_div_const (by positivity))
  have h3 := (Real.tendsto_exp_atBot.comp h2).const_mul (2 * Real.sqrt (400 * Real.exp 1 * Real.pi))
  simpa using h3

