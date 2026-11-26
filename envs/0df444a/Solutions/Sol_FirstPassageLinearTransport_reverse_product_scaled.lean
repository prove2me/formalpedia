-- Prove2me | solution 1 for FirstPassageLinearTransport.reverse_product_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:45.904019+00:00
-- url     : https://prove2.me/submissions/566ded30-a736-457e-ad9e-72bef0092fd0

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_succ
import Theorems.Thm_FirstPassageLinearTransport_reverse_step_scaled
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
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
theorem _root_.solution {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (3 : ℚ) ^ (oddCount n h) * (n : ℚ) =
      (2 : ℚ) ^ h * (orbit h n : ℚ) * reverseProduct n h := by
  induction h with
  | zero => simp [reverseProduct]
  | succ h ih =>
      have hlocal :
          (3 : ℚ) ^ (parityBit n h : ℕ) * (orbit h n : ℚ) =
            2 * (orbit (h + 1) n : ℚ) * reverseStepFactor n h := by
        simpa [reverseStepFactor, parityBit, orbit_succ] using
          reverse_step_scaled (orbit_pos hn h)
      rw [oddCount_succ, reverseProduct_succ]
      calc
        (3 : ℚ) ^ (oddCount n h + (parityBit n h : ℕ)) * (n : ℚ) =
            (3 : ℚ) ^ (parityBit n h : ℕ) *
              ((3 : ℚ) ^ (oddCount n h) * (n : ℚ)) := by
                rw [pow_add]
                ring
        _ = (3 : ℚ) ^ (parityBit n h : ℕ) *
              ((2 : ℚ) ^ h * (orbit h n : ℚ) * reverseProduct n h) := by
                rw [ih]
        _ = (2 : ℚ) ^ h *
              ((3 : ℚ) ^ (parityBit n h : ℕ) * (orbit h n : ℚ)) *
                reverseProduct n h := by ring
        _ = (2 : ℚ) ^ h *
              (2 * (orbit (h + 1) n : ℚ) * reverseStepFactor n h) *
                reverseProduct n h := by rw [hlocal]
        _ = (2 : ℚ) ^ (h + 1) * (orbit (h + 1) n : ℚ) *
              (reverseProduct n h * reverseStepFactor n h) := by
                rw [pow_succ]
                ring
end FirstPassageLinearTransport
