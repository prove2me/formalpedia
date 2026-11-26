-- Prove2me | solution 1 for FirstPassageLinearTransport.rawOrbit_two_eq_shortcut_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:31:38.326925+00:00
-- url     : https://prove2.me/submissions/b0ff5cdd-5e95-42a4-b088-3822ed58bc12

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_even
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_odd
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero

set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : n % 2 = 1) :
    rawOrbit 2 n = shortcut n := by
  have heven : (3 * n + 1) % 2 = 0 := by omega
  rw [show 2 = 1 + 1 by omega, rawOrbit_succ, rawOrbit_succ,
    rawOrbit_zero, rawCollatz_of_odd hn, rawCollatz_of_even heven,
    shortcut_of_odd hn]
end FirstPassageLinearTransport
