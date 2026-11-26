-- Prove2me | solution 1 for FirstPassageLinearTransport.three_rpow_maximalBarrierHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:28.415896+00:00
-- url     : https://prove2.me/submissions/ad0f6810-6189-4562-b00f-179773dd3392

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ maximalBarrierHeight t M =
      (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
  rw [three_rpow_eq_two_rpow_logTwoThree]
  congr 1
  unfold maximalBarrierHeight
  have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
  field_simp [hlog]
end FirstPassageLinearTransport
