-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassage_odd_following_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:49.425778+00:00
-- url     : https://prove2.me/submissions/092b9cf8-94e8-4f6f-9d3a-b225540f0865

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_shortcut_gt_of_odd
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
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
theorem _root_.solution {Y n h i : ℕ}
    (hfp : IsFirstPassage Y n h) (hi : i < h)
    (hodd : (parityBit n i : ℕ) = 1) :
    Y < orbit (i + 1) n := by
  have hprev : Y < orbit i n := hfp.2 i hi
  have hparity : orbit i n % 2 = 1 := hodd
  have hinc := shortcut_gt_of_odd hparity
  simpa [orbit_succ] using hprev.trans hinc
end FirstPassageLinearTransport
