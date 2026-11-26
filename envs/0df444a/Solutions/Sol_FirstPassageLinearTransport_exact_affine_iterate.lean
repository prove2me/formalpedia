-- Prove2me | solution 1 for FirstPassageLinearTransport.exact_affine_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:37.791255+00:00
-- url     : https://prove2.me/submissions/8594d178-cacc-462e-8c23-626ff75b9cb8

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_exact_affine_iterate_scaled
import Theorems.Thm_FirstPassageLinearTransport_affineCorrection_cast_div
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
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (n k : ℕ) :
    (orbit k n : ℚ) =
      (3 : ℚ) ^ (oddCount n k) / (2 : ℚ) ^ k * (n : ℚ) +
        affineCorrectionQ n k := by
  rw [← affineCorrection_cast_div]
  rw [div_mul_eq_mul_div, ← add_div]
  have hpow : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (eq_div_iff hpow).2
  have hscaled :
      (2 : ℚ) ^ k * (orbit k n : ℚ) =
        (3 : ℚ) ^ (oddCount n k) * (n : ℚ) +
          (affineCorrection n k : ℚ) := by
    exact_mod_cast exact_affine_iterate_scaled n k
  simpa [mul_comm] using hscaled
end FirstPassageLinearTransport
