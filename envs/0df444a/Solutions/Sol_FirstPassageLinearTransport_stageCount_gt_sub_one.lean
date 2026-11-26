-- Prove2me | solution 1 for FirstPassageLinearTransport.stageCount_gt_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:27.162675+00:00
-- url     : https://prove2.me/submissions/7d76d893-664e-43d3-b7fb-784e99601521

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {omega : ℝ} (M : ℕ) :
    omega * Real.log (M + 4) - 1 < stageCount omega M := by
  unfold stageCount
  exact Nat.sub_one_lt_floor _
end FirstPassageLinearTransport
