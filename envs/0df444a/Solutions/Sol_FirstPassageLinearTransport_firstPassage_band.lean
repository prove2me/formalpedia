-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassage_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:56.996492+00:00
-- url     : https://prove2.me/submissions/addaaa59-d266-44cb-b07e-3c29cbf4136c

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_final_even
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
theorem _root_.solution {Y n h : ℕ} (hh : 0 < h)
    (hfp : IsFirstPassage Y n h) :
    Y < 2 * orbit h n ∧ orbit h n ≤ Y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have heven := firstPassage_final_even hfp
  have hstep : 2 * orbit (k + 1) n = orbit k n := by
    simpa [orbit_succ] using two_mul_shortcut_of_even heven
  constructor
  · have hprev : Y < orbit k n := hfp.2 k (by omega)
    have hband : Y < 2 * orbit (k + 1) n := by omega
    simpa [Nat.succ_eq_add_one] using hband
  · simpa [Nat.succ_eq_add_one] using hfp.1
end FirstPassageLinearTransport
