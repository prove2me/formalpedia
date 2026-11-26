-- Prove2me | solution 1 for FirstPassageLinearTransport.continuous_binaryBarrierRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:34.400798+00:00
-- url     : https://prove2.me/submissions/64c9d45c-6a7f-4827-8b49-28d9aa884d02

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : Continuous binaryBarrierRate := by
  unfold binaryBarrierRate
  fun_prop
end FirstPassageLinearTransport
