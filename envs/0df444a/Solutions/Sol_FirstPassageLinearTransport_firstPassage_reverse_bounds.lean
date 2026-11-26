-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassage_reverse_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:07.685004+00:00
-- url     : https://prove2.me/submissions/a74c5511-37ee-4613-b8fb-b5441e68ac98

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverse_product_identity
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_bounds
import Theorems.Thm_FirstPassageLinearTransport_reverseScale_nonneg
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
theorem _root_.solution {Y n h : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    (1 - (h : ℚ) / (2 * (Y : ℚ))) * reverseScale n h ≤ (n : ℚ) ∧
      (n : ℚ) ≤ reverseScale n h := by
  have hp := reverseProduct_bounds hn hY hfp
  have hA := reverseScale_nonneg n h
  have hid : (n : ℚ) = reverseScale n h * reverseProduct n h := by
    simpa [reverseScale] using reverse_product_identity hn h
  rw [hid]
  constructor
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hp.1 hA
  · simpa using mul_le_mul_of_nonneg_left hp.2 hA
end FirstPassageLinearTransport
