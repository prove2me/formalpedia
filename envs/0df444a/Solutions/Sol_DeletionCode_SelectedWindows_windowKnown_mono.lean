-- Prove2me | solution 1 for DeletionCode.SelectedWindows.windowKnown_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:03:18.411181+00:00
-- url     : https://prove2.me/submissions/3d92cf72-5791-4173-a05b-0b292df2dcb0

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s t : Memory) (start len : ℕ)
    (hext : Extends s t) (h : WindowKnown s start len) :
    WindowKnown t start len := by
  apply (windowKnown_iff _ _ _).mpr
  intro i hi
  obtain ⟨b, hb⟩ := (windowKnown_iff _ _ _).mp h i hi
  exact ⟨b, hext (start + i) b hb⟩
end DeletionCode.SelectedWindows
