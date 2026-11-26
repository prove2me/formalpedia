-- Prove2me | solution 1 for FirstPassageLinearTransport.reverseProduct_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:30.409814+00:00
-- url     : https://prove2.me/submissions/fc70b793-d747-4f1b-9d11-ddec4e2c8c50

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_eq_prod_loss
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_nonneg
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverseLoss_le_firstPassage
import Theorems.Thm_FirstPassageLinearTransport_one_sub_sum_le_prod
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
    1 - (h : ℚ) / (2 * (Y : ℚ)) ≤ reverseProduct n h ∧
      reverseProduct n h ≤ 1 := by
  have hloss :
      ∀ i ∈ Finset.range h, 0 ≤ reverseLoss n i ∧ reverseLoss n i ≤ 1 := by
    intro i hi
    exact ⟨reverseLoss_nonneg n i, reverseLoss_le_one hn i⟩
  have hsum :
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
        (h : ℚ) / (2 * (Y : ℚ)) := by
    calc
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
          ∑ _i ∈ Finset.range h, (1 / (2 * (Y : ℚ)) : ℚ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact reverseLoss_le_firstPassage hY hfp (Finset.mem_range.mp hi)
      _ = (h : ℚ) / (2 * (Y : ℚ)) := by
        simp
        ring
  rw [reverseProduct_eq_prod_loss]
  constructor
  · calc
      1 - (h : ℚ) / (2 * (Y : ℚ)) ≤
          1 - ∑ i ∈ Finset.range h, reverseLoss n i := by linarith
      _ ≤ ∏ i ∈ Finset.range h, (1 - reverseLoss n i) :=
        one_sub_sum_le_prod _ _ hloss
  · apply Finset.prod_le_one
    · intro i hi
      exact sub_nonneg.mpr (hloss i hi).2
    · intro i hi
      linarith [(hloss i hi).1]
end FirstPassageLinearTransport
