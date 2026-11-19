-- Prove2me | solution 1 for DeletionCode.SelectedWindows.all_windows_known
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:14.796178+00:00
-- url     : https://prove2.me/submissions/657f5d7c-1f3f-4bd2-a2d2-80417aff5ecd

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s : Memory) (D L : ℕ) (hD : D ≤ L)
    (hknown : ∀ w : Slot, WindowKnown s (windowStart D w) L) :
    WindowKnown s 0 (L + D) := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  by_cases hfirst : i < L
  · have hread := (windowKnown_iff _ _ _).mp (hknown ⟨0, by omega⟩) i hfirst
    simpa [windowStart] using hread
  · have hiD : D ≤ i := by omega
    have hiL : i - D < L := by omega
    have hread := (windowKnown_iff _ _ _).mp (hknown ⟨2, by omega⟩) (i - D) hiL
    simpa [windowStart, show D + (i - D) = i by omega] using hread
end DeletionCode.SelectedWindows
