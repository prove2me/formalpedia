-- Prove2me | solution 1 for DeletionCode.PathMemory.readPath_exists_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:59.901863+00:00
-- url     : https://prove2.me/submissions/5f25900f-d9ec-4967-b533-053ece34c647

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_subblock


set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
namespace DeletionCode.PathMemory
theorem _root_.solution (k : ℕ) (h : Header) (s : Memory)
    (side : Bool) (start len : ℕ)
    (hknown : WindowKnown s 0 (negativeLength k h))
    (hbound : start + len ≤ pathLength k h side) :
    ∃ bits, readPath k h s side start len = some bits := by
  cases side with
  | false =>
    have hbound' : start + len ≤ negativeLength k h := hbound
    obtain ⟨bits, hbits⟩ := windowKnown_subblock s 0 (negativeLength k h)
      start len hknown (Nat.zero_le start) (by simpa only [Nat.zero_add] using hbound')
    exact ⟨bits, by simpa only [readPath, if_pos hbound'] using hbits⟩
  | true =>
    have hbound' : start + len ≤ positiveLength k h := hbound
    obtain ⟨negative, hnegative⟩ := hknown
    refine ⟨extractBits (rebuildPositiveFinite k h negative) start len hbound', ?_⟩
    simp only [readPath, dif_pos hbound', hnegative, Option.map_some]
end DeletionCode.PathMemory
