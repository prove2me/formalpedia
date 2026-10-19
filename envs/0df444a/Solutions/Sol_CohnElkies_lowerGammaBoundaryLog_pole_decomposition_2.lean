-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_pole_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:24.858143+00:00
-- url     : https://prove2.me/submissions/e20cdd93-8c71-480c-84bb-8ba59598b3f1

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


theorem solution
    (ℓ R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ℓ R y =
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ -
        Real.log (|y| / 2) := by
  unfold lowerGammaBoundaryLog
  set w : ℂ := -Complex.I * (y : ℂ) / 2 with hwdef
  have hwim : w.im = -y / 2 := by simp [hwdef]
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; exact hy this
  have hwG : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.im h
    rw [hwim] at this; simp at this; exact hy this
  have h1 : (1 : ℂ) - Complex.I * (y : ℂ) / 2 = w + 1 := by rw [hwdef]; ring
  have hnw : ‖w‖ = |y| / 2 := by
    rw [hwdef]; simp [abs_div]
  rw [h1, Complex.Gamma_add_one w hw0, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr hwG), hnw]
  ring

