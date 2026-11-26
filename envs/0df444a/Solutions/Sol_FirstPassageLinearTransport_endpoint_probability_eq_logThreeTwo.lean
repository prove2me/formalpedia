-- Prove2me | solution 1 for FirstPassageLinearTransport.endpoint_probability_eq_logThreeTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:14:56.649292+00:00
-- url     : https://prove2.me/submissions/10bef73b-87fe-4d19-89dd-ffd1c08173c7

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    1 / 2 + firstPassageEndpointDisplacement = logThreeTwo := by
  unfold firstPassageEndpointDisplacement driftGap a0 logTwoThree logThreeTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2, hlog3]
  ring
end FirstPassageLinearTransport
