-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_tendsto_zero_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:17.907221+00:00
-- url     : https://prove2.me/submissions/857177a7-8f25-4072-9481-c436c0077c39

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


theorem solution
    (T : ℝ) :
    Tendsto (fun σ : ℝ => stripPoissonKernel σ T)
      (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hden : (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (Real.pi * (1 + 1) / 2))) ≠ 0 := by
    rw [show Real.pi * (1 + 1) / 2 = Real.pi by ring, Real.cos_pi]
    have := Real.cosh_pos (Real.pi * T / 2)
    linarith
  have hc : ContinuousAt (fun σ : ℝ => stripPoissonKernel σ T) 1 := by
    unfold stripPoissonKernel stripAngle
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have h := hc.tendsto
  have hv : stripPoissonKernel 1 T = 0 := by
    unfold stripPoissonKernel stripAngle
    rw [show Real.pi * (1 + 1) / 2 = Real.pi by ring, Real.sin_pi, zero_div]
  rw [hv] at h
  exact h

