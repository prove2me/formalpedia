-- Prove2me | solution 1 for FirstPassageLinearTransport.centralOrbitScale_eq_two_rpow_neg_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:37.214974+00:00
-- url     : https://prove2.me/submissions/4c6c37b0-1664-4a92-bb4e-2d99142ab18c

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k : ℕ) :
    centralOrbitScale k = (2 : ℝ) ^ (-driftGap * k) := by
  unfold centralOrbitScale
  rw [three_rpow_eq_two_rpow_logTwoThree, ← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold driftGap a0
  ring
end FirstPassageLinearTransport
