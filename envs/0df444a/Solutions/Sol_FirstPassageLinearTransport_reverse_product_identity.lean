-- Prove2me | solution 1 for FirstPassageLinearTransport.reverse_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:33.475799+00:00
-- url     : https://prove2.me/submissions/c3ccd965-5e2a-4ce3-a4ca-ae2dd28bd7d1

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverse_product_scaled
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
theorem _root_.solution {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (n : ℚ) =
      ((2 : ℚ) ^ h * (orbit h n : ℚ) /
        (3 : ℚ) ^ (oddCount n h)) * reverseProduct n h := by
  have hthree : (3 : ℚ) ^ (oddCount n h) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hthree).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using reverse_product_scaled hn h
end FirstPassageLinearTransport
