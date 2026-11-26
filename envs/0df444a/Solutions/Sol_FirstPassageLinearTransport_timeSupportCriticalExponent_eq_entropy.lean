-- Prove2me | solution 1 for FirstPassageLinearTransport.timeSupportCriticalExponent_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:17.070811+00:00
-- url     : https://prove2.me/submissions/825873ed-680b-4414-a64e-d2c354fbe40f

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogCriticalExponent_eq_entropy
import Theorems.Thm_FirstPassageLinearTransport_fixedPolylogCriticalExponent_gt_one


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    timeSupportCriticalExponent =
      1 / (2 * (1 - binaryEntropyBaseTwo logThreeTwo)) := by
  rw [timeSupportCriticalExponent, fixedPolylogCriticalExponent_eq_entropy]
  have hden : 1 - binaryEntropyBaseTwo logThreeTwo ≠ 0 := by
    intro hz
    have hEq := fixedPolylogCriticalExponent_eq_entropy
    rw [hz] at hEq
    norm_num at hEq
    linarith [fixedPolylogCriticalExponent_gt_one]
  field_simp [hden]
end FirstPassageLinearTransport
