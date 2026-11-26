-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseLossTotal_le_div_of_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:45.514994+00:00
-- url     : https://prove2.me/submissions/e7112673-3df9-452b-8065-0600b8c25e35

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Y n h : ℕ} {D : ℚ} (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    reverseLossTotal n h ≤ D / (Y : ℚ) := by
  have hYQ : (0 : ℚ) < Y := by exact_mod_cast hY
  apply (le_div_iff₀ hYQ).2
  simpa [scaledReverseLoss, mul_comm] using hloss
end FirstPassageLinearTransport
