-- Prove2me | solution 1 for DeletionCode.PathMemory.readPath_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:29.818423+00:00
-- url     : https://prove2.me/submissions/77839478-0c97-4718-bb43-e4cdbc4d2dc6

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
import Theorems.Thm_DeletionCode_PathMemory_readPath_sound
import Theorems.Thm_DeletionCode_PathMemory_readPath_exists_of_complete

set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
namespace DeletionCode.PathMemory
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits ∧
      Matches bits (pathLetters k h long side) start := by
  obtain ⟨bits, hread⟩ := readPath_exists_of_complete k h s side start len hknown hbound
  exact ⟨bits, hread, readPath_sound k h long s side start len bits
    hrho0 hrho1 hbit hs hread⟩
end DeletionCode.PathMemory
