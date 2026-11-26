-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrierHeight_eq_displacement_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:09.139309+00:00
-- url     : https://prove2.me/submissions/db724678-e5c2-4f2d-b5ab-37baaa216b7b

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (lambda t : ℝ) (M : ℕ) :
    adjustableBarrierHeight lambda t M =
      adjustableBarrierDisplacement lambda t * (M : ℝ) := by
  unfold adjustableBarrierHeight adjustableBarrierDisplacement
  ring
end FirstPassageLinearTransport
