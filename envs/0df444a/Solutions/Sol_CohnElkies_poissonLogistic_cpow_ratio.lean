-- Prove2me | solution 1 for CohnElkies.poissonLogistic_cpow_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ccefb11d-2f03-4507-a756-9250775e7605

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_mem_Ioo
import Theorems.Thm_CohnElkies_poissonLogistic_odds

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) (w : ℂ) :
    ((poissonLogistic u : ℝ) : ℂ) ^ w *
        (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w)) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
  have hx := poissonLogistic_mem_Ioo u
  have hfirst : (poissonLogistic u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx.1)
  have hsecond : ((1 - poissonLogistic u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hx.2))
  have hlog :
      Real.log (poissonLogistic u) -
        Real.log (1 - poissonLogistic u) =
          Real.pi * u := by
    rw [← Real.log_div (ne_of_gt hx.1)
      (ne_of_gt (sub_pos.mpr hx.2)),
      poissonLogistic_odds, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hfirst,
    Complex.cpow_def_of_ne_zero hsecond, ← Complex.exp_add,
    ← Complex.ofReal_log hx.1.le,
    ← Complex.ofReal_log (sub_pos.mpr hx.2).le]
  congr 1
  calc
    ((Real.log (poissonLogistic u) : ℝ) : ℂ) * w +
        ((Real.log (1 - poissonLogistic u) : ℝ) : ℂ) * (-w) =
      ((Real.log (poissonLogistic u) -
        Real.log (1 - poissonLogistic u) : ℝ) : ℂ) * w := by
          push_cast
          ring
    _ = ((Real.pi * u : ℝ) : ℂ) * w := by
      rw [hlog]
end CohnElkies
