-- Prove2me | solution 1 for DeletionCode.SelectedWindows.windowKnown_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:01:21.632293+00:00
-- url     : https://prove2.me/submissions/06c75eae-279e-4d69-a295-b823d7f5a3ca

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_PartialWords_readBits_eq_some_iff


set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s : Memory) (start len : ℕ) :
    WindowKnown s start len ↔ ∀ i, i < len → ∃ b, s (start + i) = some b := by
  constructor
  · rintro ⟨bits, hread⟩ i hi
    exact ⟨bits ⟨i, hi⟩, (readBits_eq_some_iff s start len bits).mp hread ⟨i, hi⟩⟩
  · intro h
    refine ⟨fun i => (s (start + i.val)).getD false, ?_⟩
    apply (readBits_eq_some_iff _ _ _ _).mpr
    intro i
    obtain ⟨b, hb⟩ := h i.val i.isLt
    simp [hb]
end DeletionCode.SelectedWindows
