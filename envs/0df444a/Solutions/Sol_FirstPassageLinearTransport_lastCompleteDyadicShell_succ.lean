-- Prove2me | solution 1 for FirstPassageLinearTransport.lastCompleteDyadicShell_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:24.917957+00:00
-- url     : https://prove2.me/submissions/f5114008-d2e8-4bcc-98ba-5ec8c4a83ec9

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {X : ℕ} (hX : 4 ≤ X) :
    lastCompleteDyadicShell X + 1 = Nat.log 2 X := by
  have hlog : 1 ≤ Nat.log 2 X := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  unfold lastCompleteDyadicShell
  omega
end FirstPassageLinearTransport
