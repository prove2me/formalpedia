-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_tendsto_zero_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/548f1e04-5737-463a-85e1-662eb52c5d2c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    (T : ℝ) :
    Tendsto (fun σ : ℝ => stripPoissonKernel σ T)
      (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hangle : stripAngle (1 : ℝ) = Real.pi := by
    unfold stripAngle
    ring
  have hden :
      4 * (Real.cosh (Real.pi * T / 2) -
        Real.cos (stripAngle (1 : ℝ))) ≠ 0 := by
    rw [hangle, Real.cos_pi]
    have hcosh := Real.one_le_cosh (Real.pi * T / 2)
    nlinarith
  have hnum : ContinuousAt
      (fun σ : ℝ => Real.sin (stripAngle σ)) 1 := by
    unfold stripAngle
    fun_prop
  have hdencont : ContinuousAt
      (fun σ : ℝ =>
        4 * (Real.cosh (Real.pi * T / 2) -
          Real.cos (stripAngle σ))) 1 := by
    unfold stripAngle
    fun_prop
  have h := (hnum.div hdencont hden).tendsto
  simpa [stripPoissonKernel, hangle, Real.sin_pi] using! h
end CohnElkies
