-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseProduct_eq_prod_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:56.734849+00:00
-- url     : https://prove2.me/submissions/8f5427c4-bfb2-4c6a-9980-0dfd5b5e3e04

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverseStepFactor_eq_one_sub_reverseLoss
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
theorem _root_.solution (n h : ℕ) :
    reverseProduct n h =
      ∏ i ∈ Finset.range h, (1 - reverseLoss n i) := by
  simp [reverseProduct, reverseStepFactor_eq_one_sub_reverseLoss]
end FirstPassageLinearTransport
