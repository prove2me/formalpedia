-- Prove2me | solution 1 for FirstPassageLinearTransport.lastCompleteDyadicShell_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:42.955418+00:00
-- url     : https://prove2.me/submissions/5e9cc916-96ab-4cd1-889e-cbe9135769c5

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_lastCompleteDyadicShell_succ


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {X : ℕ} (hX : 4 ≤ X) :
    lastCompleteDyadicShell X + 2 = Nat.log 2 X + 1 := by
  have h := lastCompleteDyadicShell_succ hX
  omega
end FirstPassageLinearTransport
