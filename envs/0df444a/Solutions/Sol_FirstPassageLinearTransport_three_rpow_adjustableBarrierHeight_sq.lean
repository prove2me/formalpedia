-- Prove2me | solution 1 for FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:15.730852+00:00
-- url     : https://prove2.me/submissions/32a6dd89-0787-42d9-b06c-f64ae9031cf3

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by
  rw [three_rpow_adjustableBarrierHeight, ← Real.rpow_add (by norm_num)]
  congr 1
  ring
end FirstPassageLinearTransport
