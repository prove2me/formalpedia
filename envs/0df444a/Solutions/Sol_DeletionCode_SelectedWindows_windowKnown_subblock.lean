-- Prove2me | solution 1 for DeletionCode.SelectedWindows.windowKnown_subblock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:08:41.47948+00:00
-- url     : https://prove2.me/submissions/1bddcbfd-c19c-418d-a982-8f2d6779dec6

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s : Memory) (a m b len : ℕ)
    (h : WindowKnown s a m) (hab : a ≤ b) (hbound : b + len ≤ a + m) :
    WindowKnown s b len := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  have hidx : b + i - a < m := by omega
  have hread := (windowKnown_iff _ _ _).mp h (b + i - a) hidx
  simpa [show a + (b + i - a) = b + i by omega] using hread
end DeletionCode.SelectedWindows
