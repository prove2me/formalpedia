-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotMultiplier_finTwoEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:12.796566+00:00
-- url     : https://prove2.me/submissions/87c05490-a097-41f8-813a-70926060afc4

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (b : Fin 2) :
    ballotMultiplier (finTwoEquiv b) = (3 : ℝ) ^ (b : ℕ) / 2 := by
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases hb with hb | hb
  · have hbeq : b = 0 := Fin.ext hb
    subst b
    norm_num [ballotMultiplier, finTwoEquiv]
  · have hbeq : b = 1 := Fin.ext hb
    subst b
    norm_num [ballotMultiplier, finTwoEquiv]
end FirstPassageLinearTransport
