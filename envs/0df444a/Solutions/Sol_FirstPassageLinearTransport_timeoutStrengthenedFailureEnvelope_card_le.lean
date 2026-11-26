-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutStrengthenedFailureEnvelope_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:03.001404+00:00
-- url     : https://prove2.me/submissions/82fa284d-d32e-4333-9ed8-10b51ad56c41

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (M L S : ℕ) (R : ℝ) :
    (timeoutStrengthenedFailureEnvelope P K₀ M L S R).card ≤
      (timeoutSeparatedFailureEnvelope P K₀ M L S).card +
        (shellMultiplicativeHit M (R / 4)).card := by
  exact Finset.card_union_le _ _
end FirstPassageLinearTransport
