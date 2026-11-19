-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.complete_wordKnown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:50.878172+00:00
-- url     : https://prove2.me/submissions/404d81f8-b71f-440e-b019-9a9f2d309aec

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_all_windows_known

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution (s : State B) (mem : B → Memory) (D : B → ℕ)
    (k : ℕ) (hreal : Realizes s mem D k) (b : B)
    (hD : D b ≤ 3 * (k + 1)) (hcomplete : s.Complete b) :
    WindowKnown (mem b) 0 (3 * (k + 1) + D b) := by
  exact all_windows_known (mem b) (D b) (3 * (k + 1)) hD
    (fun w => hreal.done_known b w (hcomplete w))
end Realizes
end DeletionCode.SelectedWindows
