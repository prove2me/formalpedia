-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:01.13412+00:00
-- url     : https://prove2.me/submissions/7f0c12af-01a9-4814-be75-9855506f8c50

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_add
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
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
theorem _root_.solution (n k j : ℕ) :
    oddCount n (k + j) = oddCount n k + oddCount (orbit k n) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show k + (j + 1) = (k + j) + 1 by omega,
        oddCount_succ, ih, oddCount_succ, parityBit_add]
      omega
end FirstPassageLinearTransport
