-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalBarrierC0_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:22.243458+00:00
-- url     : https://prove2.me/submissions/d2dbc166-c6f2-4f25-8956-00a4795d30da

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < maximalBarrierC0 := by
  unfold maximalBarrierC0
  exact div_pos (by norm_num)
    (mul_pos (by norm_num) (sq_pos_of_pos logTwoThree_pos))
end FirstPassageLinearTransport
