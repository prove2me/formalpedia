-- Prove2me | solution 2 for CohnElkies.lowerWallis_arg_one_sub_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:16:31.19068+00:00
-- url     : https://prove2.me/submissions/971d4c8e-f24d-44cd-a1be-d79945d6d3cb

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


theorem solution (u : ℝ) :
    Complex.arg (1 - Complex.I * (u : ℂ)) =
      -Real.arctan u := by
  have hre : (1 - Complex.I * (u:ℂ)).re = 1 := by simp
  have him : (1 - Complex.I * (u:ℂ)).im = -u := by simp
  have hn : ‖1 - Complex.I * (u:ℂ)‖ = Real.sqrt (1 + u^2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]; congr 1; ring
  rw [Complex.arg_of_re_nonneg (by rw [hre]; norm_num), him, hn, ← Real.arctan_neg,
    Real.arctan_eq_arcsin, neg_sq]

