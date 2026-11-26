-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseStepFactor_eq_one_sub_reverseLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:08.655949+00:00
-- url     : https://prove2.me/submissions/9474b306-ec4a-41fb-b2b1-ec86dba44ec3

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
theorem _root_.solution (n i : ℕ) :
    reverseStepFactor n i = 1 - reverseLoss n i := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp [reverseStepFactor, reverseOddFactor, reverseLoss, hodd]
  · simp [reverseStepFactor, reverseOddFactor, reverseLoss, hodd]
end FirstPassageLinearTransport
