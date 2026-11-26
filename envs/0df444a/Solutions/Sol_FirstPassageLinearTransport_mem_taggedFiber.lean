-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_taggedFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:48.288441+00:00
-- url     : https://prove2.me/submissions/b793cde3-a285-4ab9-8869-af7a107ffdd2

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y h y n : ℕ} :
    n ∈ taggedFiber M Y h y ↔
      n ∈ dyadicShell M ∧ IsFirstPassage Y n h ∧ orbit h n = y := by
  classical
  simp [taggedFiber, and_assoc]
end FirstPassageLinearTransport
