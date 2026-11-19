-- Prove2me | solution 1 for DeletionCode.ConcreteStart.startPositive_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:30.31752+00:00
-- url     : https://prove2.me/submissions/7e0f3fc4-22fb-4c84-85e1-80fb3f3680a0

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeExtra_lt
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq
import Theorems.Thm_DeletionCode_HeaderRecovery_transferFinite_valid
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct
import Theorems.Thm_DeletionCode_SelectedWindows_seed_selects_window


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)
namespace DeletionCode.ConcreteStart
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (extra : Bool) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k → extra = negativePath k h long (offset + k - 1)) :
    ∃ t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by
  have hvalid := HeaderRecovery.transferFinite_valid k h long offset bits extra
    hrho0 hrho1 hbit hbound hseed hextra
  let transferred := transferFinite k h offset bits extra
  have hmatches : PartialWords.Matches transferred.2 (negativePath k h long)
      transferred.1 := fun i => (hvalid.2 i).symm
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct
    s (negativePath k h long) (negativeLength k h) transferred.1 k
    hs hvalid.1 transferred.2 hmatches
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [startPositive, if_pos hbound] using ht
  · apply seed_selects_window t (negativeExtra k h) k transferred.1
    · exact HeaderRecovery.negativeExtra_lt k h hrho0 hrho1
    · have hb := hvalid.1
      rw [HeaderRecovery.negativeLength_eq k h hrho0 hrho1] at hb
      exact hb
    · exact ⟨transferred.2, hread⟩
end DeletionCode.ConcreteStart
