-- Prove2me | solution 1 for FirstPassageLinearTransport.endpointTolerance_lt_driftGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:08.998894+00:00
-- url     : https://prove2.me/submissions/494c1cc5-0cad-4762-91ae-c60bc1807d44

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Theorems.Thm_FirstPassageLinearTransport_endpointLambda_pos
import Theorems.Thm_FirstPassageLinearTransport_endpointLambda_lt_one
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) :
    endpointTolerance n < driftGap := by
  unfold endpointTolerance
  nlinarith [driftGap_pos, endpointLambda_pos n, endpointLambda_lt_one n]
end FirstPassageLinearTransport
