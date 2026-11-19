-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.fill_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:02.359302+00:00
-- url     : https://prove2.me/submissions/96dc52b0-ce80-4d3f-bd28-56c84e0ec4d4

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_update_mem

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hwindow : WindowKnown t (windowStart (D b) w) (3 * (k + 1))) :
    Realizes (s.fill b w) (Function.update mem b t) D k := by
  apply Realizes.fill s (Function.update mem b t) D k
    (Realizes.update_mem s mem D k hreal b t hext) b w
  simpa using hwindow
end Realizes
end DeletionCode.SelectedWindows
