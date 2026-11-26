-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseLoss_le_firstPassage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:41.081341+00:00
-- url     : https://prove2.me/submissions/ebcd9f53-bb06-40c5-82ed-67db5b376402

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_odd_following_gt
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
theorem _root_.solution {Y n h i : ℕ}
    (hY : 0 < Y) (hfp : IsFirstPassage Y n h) (hi : i < h) :
    reverseLoss n i ≤ 1 / (2 * (Y : ℚ)) := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp only [reverseLoss, hodd, if_pos]
    have hnext := firstPassage_odd_following_gt hfp hi hodd
    have hdenpos : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
    have hdenle :
        (2 : ℚ) * (Y : ℚ) ≤ 2 * (orbit (i + 1) n : ℚ) := by
      exact_mod_cast (show 2 * Y ≤ 2 * orbit (i + 1) n by omega)
    exact one_div_le_one_div_of_le hdenpos hdenle
  · simp [reverseLoss, hodd]
end FirstPassageLinearTransport
