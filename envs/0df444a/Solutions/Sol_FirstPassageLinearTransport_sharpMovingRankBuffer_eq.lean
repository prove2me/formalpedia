-- Prove2me | solution 1 for FirstPassageLinearTransport.sharpMovingRankBuffer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:16:54.078414+00:00
-- url     : https://prove2.me/submissions/fabce359-0849-41de-8ec5-f872dcb2eed2

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (A : ℕ → ℝ) (M : ℕ) :
    sharpMovingRankBuffer A M =
      firstPassageEntropyGap * movingTerminalRank A M -
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) := rfl
end FirstPassageLinearTransport
