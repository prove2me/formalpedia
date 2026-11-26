-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseLoss_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:04.893668+00:00
-- url     : https://prove2.me/submissions/5ac4de0e-b099-4be7-ba83-486ea4e29970

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
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
theorem _root_.solution {n : ℕ} (hn : 0 < n) (i : ℕ) :
    reverseLoss n i ≤ 1 := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp only [reverseLoss, hodd, if_pos]
    have hxpos : 0 < orbit (i + 1) n := orbit_pos hn (i + 1)
    have hden : (1 : ℚ) ≤ 2 * (orbit (i + 1) n : ℚ) := by
      exact_mod_cast (show 1 ≤ 2 * orbit (i + 1) n by omega)
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hden
  · simp [reverseLoss, hodd]
end FirstPassageLinearTransport
