-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotMultiplier_boolParityWord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:19.953463+00:00
-- url     : https://prove2.me/submissions/25bf0e1d-7b5f-45b9-84df-c41222e917d8

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_ballotMultiplier_finTwoEquiv

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (r n : ℕ) :
    ballotMultiplier (boolParityWord (r + 1) n 0) =
      (3 : ℝ) ^ (parityBit n 0 : ℕ) / 2 := by
  exact ballotMultiplier_finTwoEquiv (parityBit n 0)
end FirstPassageLinearTransport
