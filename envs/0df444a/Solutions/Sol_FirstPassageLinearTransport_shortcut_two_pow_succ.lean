-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_two_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:04.879566+00:00
-- url     : https://prove2.me/submissions/fe61e5c2-8236-4753-b13c-145b5ad7589d

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution (k : ℕ) :
    shortcut (2 ^ (k + 1)) = 2 ^ k := by
  rw [shortcut_of_even]
  · rw [pow_succ]
    omega
  · rw [pow_succ]
    omega
end FirstPassageLinearTransport
