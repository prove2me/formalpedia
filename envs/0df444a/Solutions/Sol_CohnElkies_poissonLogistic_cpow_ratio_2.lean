-- Prove2me | solution 2 for CohnElkies.poissonLogistic_cpow_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:41.475395+00:00
-- url     : https://prove2.me/submissions/af80f764-3251-4131-a76a-d8591ea6b7a8

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


theorem solution (u : ℝ) (w : ℂ) :
    ((poissonLogistic u : ℝ) : ℂ) ^ w *
        (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w)) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
  have he := Real.exp_pos (Real.pi * u)
  have hp : 0 < poissonLogistic u := by unfold poissonLogistic; positivity
  have hq : 1 - poissonLogistic u = 1 / (1 + Real.exp (Real.pi * u)) := by
    unfold poissonLogistic; field_simp; ring
  have hq' : 0 < 1 - poissonLogistic u := by rw [hq]; positivity
  have hratio : poissonLogistic u / (1 - poissonLogistic u) = Real.exp (Real.pi * u) := by
    rw [hq]; unfold poissonLogistic; field_simp
  have hlog : Real.log (poissonLogistic u) - Real.log (1 - poissonLogistic u) = Real.pi * u := by
    rw [← Real.log_div hp.ne' hq'.ne', hratio, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq'.ne'), ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hp.le, ← Complex.ofReal_log hq'.le]
  calc (Real.log (poissonLogistic u) : ℂ) * w + (Real.log (1 - poissonLogistic u) : ℂ) * -w
      = ((Real.log (poissonLogistic u) - Real.log (1 - poissonLogistic u) : ℝ) : ℂ) * w := by
        push_cast; ring
    _ = ((Real.pi * u : ℝ) : ℂ) * w := by rw [hlog]

