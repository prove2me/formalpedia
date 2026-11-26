-- Prove2me | solution 1 for FirstPassageLinearTransport.endpointLambda_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:24.460074+00:00
-- url     : https://prove2.me/submissions/8402406a-b755-4ab6-a9ff-4275fb54a4eb

import Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
import Definitions.Def_FirstPassageLinearTransport_Constants
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) : endpointLambda n < 1 := by
  unfold endpointLambda
  have hinv : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith
end FirstPassageLinearTransport
