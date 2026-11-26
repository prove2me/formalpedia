-- Prove2me | solution 1 for FirstPassageLinearTransport.rankWeight_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:57.231819+00:00
-- url     : https://prove2.me/submissions/7598d86f-57b0-4dcd-a8f5-406b9917cdff

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
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
theorem _root_.solution (q d : ℕ) :
    q + (d + 1) + 2 ≤ 2 ^ d * (q + 3) := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        q + (d + 1 + 1) + 2 ≤ 2 * (q + (d + 1) + 2) := by omega
        _ ≤ 2 * (2 ^ d * (q + 3)) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (d + 1) * (q + 3) := by
          rw [pow_succ]
          ring
end FirstPassageLinearTransport
