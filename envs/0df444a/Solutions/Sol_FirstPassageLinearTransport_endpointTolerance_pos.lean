-- Prove2me | solution 1 for FirstPassageLinearTransport.endpointTolerance_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:03.950849+00:00
-- url     : https://prove2.me/submissions/ae74c8b0-c5fd-4c17-aa6f-f5b32a76d116

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_endpointLambda_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) : 0 < endpointTolerance n := by
  unfold endpointTolerance
  exact mul_pos driftGap_pos (endpointLambda_pos n)
end FirstPassageLinearTransport
