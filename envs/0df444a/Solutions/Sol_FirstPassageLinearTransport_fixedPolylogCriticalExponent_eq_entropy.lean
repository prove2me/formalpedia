-- Prove2me | solution 1 for FirstPassageLinearTransport.fixedPolylogCriticalExponent_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:29.321038+00:00
-- url     : https://prove2.me/submissions/2627279c-553a-4ffd-a82e-7ca97455f952

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_endpoint_probability_eq_logThreeTwo
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    fixedPolylogCriticalExponent =
      1 / (1 - binaryEntropyBaseTwo logThreeTwo) := by
  rw [fixedPolylogCriticalExponent, firstPassageEndpointRate,
    binaryBarrierRate, endpoint_probability_eq_logThreeTwo]
  unfold binaryEntropyBaseTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hrate : Real.log 2 - Real.binEntropy logThreeTwo ≠ 0 := by
    have hpos := firstPassageEndpointRate_pos
    rw [firstPassageEndpointRate, binaryBarrierRate] at hpos
    change 0 < Real.log 2 - Real.binEntropy
      (1 / 2 + firstPassageEndpointDisplacement) at hpos
    rw [endpoint_probability_eq_logThreeTwo] at hpos
    exact ne_of_gt hpos
  field_simp [hlog2, hrate]
end FirstPassageLinearTransport
