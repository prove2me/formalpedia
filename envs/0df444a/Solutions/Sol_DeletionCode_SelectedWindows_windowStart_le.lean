-- Prove2me | solution 1 for DeletionCode.SelectedWindows.windowStart_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:08:39.454567+00:00
-- url     : https://prove2.me/submissions/b7cf8a33-6935-4a9f-aa18-5470f07d691a

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (D : ℕ) (w : Slot) : windowStart D w ≤ D := by
  fin_cases w <;> simp [windowStart, Nat.div_le_self]
end DeletionCode.SelectedWindows
