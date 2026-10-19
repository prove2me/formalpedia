-- Prove2me | solution 2 for CohnElkies.upperGammaEuler_centered_cpow_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:37.960255+00:00
-- url     : https://prove2.me/submissions/82e7f785-5b56-4ae0-bb99-a52c42a9742d

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (m b : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ ((m : ℂ) - Complex.I * (b : ℂ)) /
        (n : ℂ) ^ (m : ℂ) =
      Complex.exp
        (-Complex.I * ((b * Real.log (n : ℝ) : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Complex.cpow_sub _ _ hn0, sub_sub_cancel_left, Complex.cpow_def_of_ne_zero hn0,
    ← Complex.natCast_log]
  congr 1
  push_cast
  ring

