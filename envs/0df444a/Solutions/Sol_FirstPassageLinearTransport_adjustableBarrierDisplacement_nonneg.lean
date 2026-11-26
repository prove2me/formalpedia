-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrierDisplacement_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:16.698673+00:00
-- url     : https://prove2.me/submissions/92ef902c-78d0-4b05-b18e-4e7fd07afa9d

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (hlambda : 0 ≤ lambda) (ht : 0 ≤ t) :
    0 ≤ adjustableBarrierDisplacement lambda t := by
  exact div_nonneg (mul_nonneg hlambda ht) logTwoThree_pos.le
end FirstPassageLinearTransport
