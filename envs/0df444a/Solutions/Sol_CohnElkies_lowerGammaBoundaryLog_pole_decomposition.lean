-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_pole_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/32495d09-d2dc-42b6-a20d-3deaa99fb560

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
    (ℓ R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ℓ R y =
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ -
        Real.log (|y| / 2) := by
  let s : ℂ := -Complex.I * (y : ℂ) / 2
  have hs : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    try dsimp [s] at him
    norm_num at him
    exact hy (by linarith)
  have hgammas : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him := congrArg Complex.im hm
    try dsimp [s] at him
    norm_num at him
    exact hy (by linarith)
  have hnorm :
      ‖Complex.Gamma (s + 1)‖ =
        ‖s‖ * ‖Complex.Gamma s‖ := by
    rw [Complex.Gamma_add_one s hs, norm_mul]
  have hs_norm : ‖s‖ = |y| / 2 := by
    simp [s, Complex.norm_real, Real.norm_eq_abs]
  have hlog :
      Real.log ‖Complex.Gamma s‖ =
        Real.log ‖Complex.Gamma (s + 1)‖ -
          Real.log (|y| / 2) := by
    rw [hnorm, Real.log_mul
      (norm_ne_zero_iff.mpr hs)
      (norm_ne_zero_iff.mpr hgammas), hs_norm]
    ring
  have harg : s + 1 = 1 - Complex.I * (y : ℂ) / 2 := by
    try dsimp [s]
    ring
  unfold lowerGammaBoundaryLog
  change
    ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma s‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ = _
  rw [hlog, harg]
  ring
end CohnElkies
