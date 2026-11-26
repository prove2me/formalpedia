-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:15.568033+00:00
-- url     : https://prove2.me/submissions/3b5afa75-ec79-46fc-9c05-3daf9214a99c

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) : shortcut n ≤ 2 * n := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [shortcut_of_even heven]
    omega
  · rw [shortcut_of_odd hodd]
    have hn : 1 ≤ n := by omega
    omega
end FirstPassageLinearTransport
