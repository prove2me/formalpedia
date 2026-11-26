-- Prove2me | solution 1 for FirstPassageLinearTransport.pow_lastCompleteDyadicShell_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:26.989131+00:00
-- url     : https://prove2.me/submissions/0abf9f84-3681-4f43-a9dc-522009a87a0c

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Theorems.Thm_FirstPassageLinearTransport_lastCompleteDyadicShell_succ

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {X : ℕ} (hX : 4 ≤ X) :
    2 ^ (lastCompleteDyadicShell X + 1) ≤ X := by
  rw [lastCompleteDyadicShell_succ hX]
  exact Nat.pow_log_le_self 2 (by omega)
end FirstPassageLinearTransport
