-- Prove2me | solution 1 for FirstPassageLinearTransport.two_mul_a0_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:49.141913+00:00
-- url     : https://prove2.me/submissions/786f3e48-d851-4252-b8ca-9a55b9f7084e

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_one_lt


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < 2 * a0 - 1 := by
  unfold a0
  linarith [logTwoThree_one_lt]
end FirstPassageLinearTransport
