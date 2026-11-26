-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageEndpointRate_lt_logTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:03.562016+00:00
-- url     : https://prove2.me/submissions/a9db378a-e1bb-49b9-b9b2-e1f23d65c487

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_lt_half

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    firstPassageEndpointRate < Real.log 2 := by
  unfold firstPassageEndpointRate binaryBarrierRate
  have hp0 : 0 < 1 / 2 + firstPassageEndpointDisplacement := by
    linarith [firstPassageEndpointDisplacement_pos]
  have hp1 : 1 / 2 + firstPassageEndpointDisplacement < 1 := by
    linarith [firstPassageEndpointDisplacement_lt_half]
  linarith [Real.binEntropy_pos hp0 hp1]
end FirstPassageLinearTransport
