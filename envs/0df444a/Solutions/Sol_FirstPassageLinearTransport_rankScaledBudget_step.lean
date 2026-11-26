-- Prove2me | solution 1 for FirstPassageLinearTransport.rankScaledBudget_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:36.308829+00:00
-- url     : https://prove2.me/submissions/1d3661a1-5588-4378-84e5-7dbf3f691435

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_rankWeight_div
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
    {q d : ℕ} {r previous newLoss : ℚ}
    (hr : 0 < r)
    (hprevious : previous ≤ ((q + (d + 1) + 2 : ℕ) : ℚ) / r)
    (hlocal : newLoss ≤ ((q + 1 : ℕ) : ℚ) / (2 * r)) :
    (1 / (2 : ℚ) ^ (d + 1)) * previous + newLoss ≤
      ((q + 2 : ℕ) : ℚ) / r := by
  have hfactor : 0 ≤ (1 / (2 : ℚ) ^ (d + 1)) := by positivity
  have hold := mul_le_mul_of_nonneg_left hprevious hfactor
  have hweight := rankWeight_div q d
  have hweightR :
      (((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1)) / r ≤
        (((q + 3 : ℕ) : ℚ) / 2) / r :=
    (div_le_div_iff_of_pos_right hr).2 hweight
  calc
    (1 / (2 : ℚ) ^ (d + 1)) * previous + newLoss ≤
        (1 / (2 : ℚ) ^ (d + 1)) *
            (((q + (d + 1) + 2 : ℕ) : ℚ) / r) +
          ((q + 1 : ℕ) : ℚ) / (2 * r) := add_le_add hold hlocal
    _ ≤ ((((q + 3 : ℕ) : ℚ) / 2) / r) +
          ((q + 1 : ℕ) : ℚ) / (2 * r) := by
      apply add_le_add
      · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hweightR
      · rfl
    _ = ((q + 2 : ℕ) : ℚ) / r := by
      field_simp [ne_of_gt hr]
      push_cast
      ring
end FirstPassageLinearTransport
