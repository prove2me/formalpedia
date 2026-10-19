-- Prove2me | solution 1 for CohnElkies.norm_nonnegative_imaginary_cpow_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/34edd11e-af59-468d-8970-db736731700a

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
    (r t : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · by_cases ht : t = 0
    · simp [ht]
    · have hexponent :
          -(Complex.I * (t : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr
          (mul_ne_zero Complex.I_ne_zero
            (Complex.ofReal_ne_zero.mpr ht))
      change ‖(0 : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1
      rw [Complex.zero_cpow hexponent]
      simp
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hrpos]
    norm_num
end CohnElkies
