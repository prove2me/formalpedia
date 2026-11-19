-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.update_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:24.754915+00:00
-- url     : https://prove2.me/submissions/3ab9ff85-d186-45ca-92ee-81a054ad3ee9

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_mono

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (t : Memory)
    (hext : Extends (mem b) t) : Realizes s (Function.update mem b t) D k := by
  apply Realizes.mono s mem (Function.update mem b t) D k hreal
  intro a
  by_cases hab : a = b
  · subst a
    simpa using hext
  · have hba : b ≠ a := Ne.symm hab
    intro j bit hj
    simpa [Function.update, hab, hba] using hj
end Realizes
end DeletionCode.SelectedWindows
