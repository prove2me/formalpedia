-- Prove2me | solution 1 for FirstPassageLinearTransport.reverse_step_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:07.530109+00:00
-- url     : https://prove2.me/submissions/646eaf90-649d-4b55-8c0d-62b971717e5f

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_pos
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    (3 : ℚ) ^ (n % 2) * (n : ℚ) =
      2 * (shortcut n : ℚ) *
        (if n % 2 = 1 then reverseOddFactor (shortcut n) else 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hstep := two_mul_shortcut_of_even heven
    simp [heven]
    exact_mod_cast hstep.symm
  · have hstep := two_mul_shortcut_of_odd hodd
    have hspos : (shortcut n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (shortcut_pos hn))
    simp only [hodd, pow_one, if_pos, reverseOddFactor]
    have hstepQ :
        (2 : ℚ) * (shortcut n : ℚ) = (3 : ℚ) * (n : ℚ) + 1 := by
      exact_mod_cast hstep
    calc
      (3 : ℚ) * (n : ℚ) = 2 * (shortcut n : ℚ) - 1 := by linarith
      _ = 2 * (shortcut n : ℚ) *
          (1 - 1 / (2 * (shortcut n : ℚ))) := by
            field_simp [hspos]
end FirstPassageLinearTransport
