-- Prove2me | solution 1 for FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:22.786166+00:00
-- url     : https://prove2.me/submissions/ace01889-38af-4b07-b152-4c4b44354db9

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (lambda * t * (M : ℝ)) := by
  rw [three_rpow_eq_two_rpow_logTwoThree]
  congr 1
  unfold adjustableBarrierHeight
  have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
  field_simp [hlog]
end FirstPassageLinearTransport
