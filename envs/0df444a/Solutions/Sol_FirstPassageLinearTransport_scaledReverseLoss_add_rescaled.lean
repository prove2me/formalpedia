-- Prove2me | solution 1 for FirstPassageLinearTransport.scaledReverseLoss_add_rescaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:40.342797+00:00
-- url     : https://prove2.me/submissions/261db4d8-cf86-4733-aaa0-49bab367e777

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Theorems.Thm_FirstPassageLinearTransport_reverseLossTotal_add
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Ylo Yhi : ℕ} (n k h : ℕ) (hYhi : 0 < Yhi) :
    scaledReverseLoss Ylo n (k + h) =
      (Ylo : ℚ) / (Yhi : ℚ) * scaledReverseLoss Yhi n k +
        scaledReverseLoss Ylo (orbit k n) h := by
  have hYhiQ : (Yhi : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hYhi)
  rw [scaledReverseLoss, reverseLossTotal_add]
  simp only [scaledReverseLoss]
  field_simp [hYhiQ]
end FirstPassageLinearTransport
