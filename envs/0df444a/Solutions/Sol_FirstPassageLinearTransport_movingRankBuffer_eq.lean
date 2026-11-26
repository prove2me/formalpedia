-- Prove2me | solution 1 for FirstPassageLinearTransport.movingRankBuffer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:23:37.914334+00:00
-- url     : https://prove2.me/submissions/ed218b67-6c4d-4f71-8c5c-44dcdb35c7b0

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
    movingRankBuffer A M =
      firstPassageEntropyGap * movingTerminalRank A M -
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
        Real.logb 2 (Real.log ((M : ℝ) + 3)) := rfl
end FirstPassageLinearTransport
