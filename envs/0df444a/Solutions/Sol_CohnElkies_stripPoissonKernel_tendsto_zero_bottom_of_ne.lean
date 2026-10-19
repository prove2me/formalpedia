-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_tendsto_zero_bottom_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/1ae88895-216b-49e5-8088-c314bb590a51

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun σ : ℝ => stripPoissonKernel σ T)
      (𝓝 (-1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hu : Real.pi * T / 2 ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero Real.pi_ne_zero hT) (by norm_num)
  have hcosh : 1 < Real.cosh (Real.pi * T / 2) :=
    Real.one_lt_cosh.mpr hu
  have hangle : Continuous (fun σ : ℝ => stripAngle σ) := by
    unfold stripAngle
    fun_prop
  have hden :
      4 * (Real.cosh (Real.pi * T / 2) -
        Real.cos (stripAngle (-1))) ≠ 0 := by
    simp only [stripAngle]
    norm_num
    linarith
  have hcontinuous :
      ContinuousAt (fun σ : ℝ => stripPoissonKernel σ T)
        (-1 : ℝ) := by
    unfold stripPoissonKernel
    exact ((Real.continuous_sin.comp hangle).continuousAt.div
      (continuousAt_const.mul
        (continuousAt_const.sub
          (Real.continuous_cos.comp hangle).continuousAt)) hden)
  convert! hcontinuous.tendsto using 1
  all_goals simp [stripPoissonKernel, stripAngle]
end CohnElkies
