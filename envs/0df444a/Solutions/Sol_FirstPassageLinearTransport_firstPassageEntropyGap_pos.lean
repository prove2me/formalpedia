-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageEntropyGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:29.176263+00:00
-- url     : https://prove2.me/submissions/9f71a923-c823-4d78-9e79-52dbee43c16d

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_eq_entropy
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < firstPassageEntropyGap := by
  have hcritical := timeSupportCriticalExponent_pos
  rw [timeSupportCriticalExponent_eq_entropy] at hcritical
  unfold firstPassageEntropyGap
  by_contra h
  have hnonpos : 1 - binaryEntropyBaseTwo logThreeTwo ≤ 0 := le_of_not_gt h
  rcases hnonpos.eq_or_lt with hzero | hneg
  · rw [hzero] at hcritical
    norm_num at hcritical
  · have hden : 2 * (1 - binaryEntropyBaseTwo logThreeTwo) < 0 := by linarith
    have hfrac : 1 / (2 * (1 - binaryEntropyBaseTwo logThreeTwo)) < 0 := by
      exact one_div_neg.mpr hden
    linarith
end FirstPassageLinearTransport
