-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageEndpointRate_eq_entropyGap_mul_logTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:17:14.747804+00:00
-- url     : https://prove2.me/submissions/98740db7-2a04-4b17-9dc7-b13773912983

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_endpoint_probability_eq_logThreeTwo


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    firstPassageEndpointRate = firstPassageEntropyGap * Real.log 2 := by
  rw [firstPassageEndpointRate, binaryBarrierRate,
    endpoint_probability_eq_logThreeTwo]
  unfold firstPassageEntropyGap binaryEntropyBaseTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]
end FirstPassageLinearTransport
