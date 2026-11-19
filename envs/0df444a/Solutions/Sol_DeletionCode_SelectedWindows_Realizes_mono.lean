-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:49.929856+00:00
-- url     : https://prove2.me/submissions/9a036cff-8a77-4ba0-bb9e-d4c8b67f6589

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_mono
import Theorems.Thm_DeletionCode_SelectedWindows_seedKnown_mono

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution (s : State B) (mem mem' : B → Memory) (D : B → ℕ) (k : ℕ)
    (hreal : Realizes s mem D k) (hext : ∀ b, Extends (mem b) (mem' b)) :
    Realizes s mem' D k where
  seed_known b w h := seedKnown_mono _ _ _ _ _ (hext b) (hreal.seed_known b w h)
  done_known b w h := windowKnown_mono _ _ _ _ (hext b) (hreal.done_known b w h)
end Realizes
end DeletionCode.SelectedWindows
