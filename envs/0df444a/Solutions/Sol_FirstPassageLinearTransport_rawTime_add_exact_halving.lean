-- Prove2me | solution 1 for FirstPassageLinearTransport.rawTime_add_exact_halving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:59.120924+00:00
-- url     : https://prove2.me/submissions/4a44eb27-e6cf-4073-8568-e5a357203bb0

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Theorems.Thm_FirstPassageLinearTransport_oddCount_two_pow_eq_zero
import Theorems.Thm_FirstPassageLinearTransport_oddCount_add


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n elapsed q v : ℕ} (heq : orbit elapsed n = 2 ^ q) (hv : v ≤ q) :
    rawTime n (elapsed + v) = rawTime n elapsed + v := by
  unfold rawTime
  rw [oddCount_add, heq, oddCount_two_pow_eq_zero hv]
  omega
end FirstPassageLinearTransport
