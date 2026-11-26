-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageEndpointDisplacement_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:49.358656+00:00
-- url     : https://prove2.me/submissions/43cd6280-c667-49a9-b39a-f177d20904b9

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    firstPassageEndpointDisplacement < 1 / 2 := by
  unfold firstPassageEndpointDisplacement
  rw [div_lt_iff₀ logTwoThree_pos]
  have htwo : logTwoThree = 2 * a0 := by
    unfold a0
    ring
  rw [htwo]
  linarith [driftGap_lt_a0]
end FirstPassageLinearTransport
