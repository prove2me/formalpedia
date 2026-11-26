-- Prove2me | solution 1 for FirstPassageLinearTransport.driftGap_lt_a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:15:12.520931+00:00
-- url     : https://prove2.me/submissions/e98e74c6-d1da-48e1-83c8-df67848fa0de

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_one_lt


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : driftGap < a0 := by
  have haHalf : (1 / 2 : ℝ) < a0 := by
    unfold a0
    linarith [logTwoThree_one_lt]
  unfold driftGap
  linarith
end FirstPassageLinearTransport
