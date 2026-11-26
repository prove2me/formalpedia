-- Prove2me | solution 1 for FirstPassageLinearTransport.three_rpow_eq_two_rpow_logTwoThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:52.264473+00:00
-- url     : https://prove2.me/submissions/e0f2c0e9-0cb8-43e4-85c3-c25c9929dc8d

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (x : ℝ) :
    (3 : ℝ) ^ x = (2 : ℝ) ^ (logTwoThree * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  unfold logTwoThree
  field_simp
end FirstPassageLinearTransport
