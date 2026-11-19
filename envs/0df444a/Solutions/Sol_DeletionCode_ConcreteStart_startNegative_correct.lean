-- Prove2me | solution 1 for DeletionCode.ConcreteStart.startNegative_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:23.775846+00:00
-- url     : https://prove2.me/submissions/a3bbb2d5-651f-4556-8520-69d7df454e40

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeExtra_lt
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct
import Theorems.Thm_DeletionCode_SelectedWindows_seed_selects_window


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)
namespace DeletionCode.ConcreteStart
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ negativeLength k h)
    (hseed : PartialWords.Matches bits (negativePath k h long) offset) :
    ∃ t, startNegative k h offset bits s = some t ∧ StartedCorrectly k h long s t := by
  obtain ⟨t, ht, hsound, hext, hread⟩ := writeBits_correct
    s (negativePath k h long) (negativeLength k h) offset k hs hbound bits hseed
  refine ⟨t, ht, hsound, hext, ?_⟩
  apply seed_selects_window t (negativeExtra k h) k offset
  · exact HeaderRecovery.negativeExtra_lt k h hrho0 hrho1
  · rw [HeaderRecovery.negativeLength_eq k h hrho0 hrho1] at hbound
    exact hbound
  · exact ⟨bits, hread⟩
end DeletionCode.ConcreteStart
