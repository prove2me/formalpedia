-- Prove2me | solution 1 for DeletionCode.PathMemory.readPath_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:38.815166+00:00
-- url     : https://prove2.me/submissions/02c7c799-d05b-49eb-9dab-6ea026e32aa0

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory

set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
namespace DeletionCode.PathMemory
theorem _root_.solution (k : ℕ) (h : Header) (s : Memory) (side : Bool)
    (start len : ℕ) (bits : PartialWords.Bits len)
    (hread : readPath k h s side start len = some bits) :
    start + len ≤ pathLength k h side := by
  cases side with
  | false =>
    simp only [readPath] at hread
    split at hread
    · assumption
    · contradiction
  | true =>
    simp only [readPath] at hread
    split at hread
    · assumption
    · contradiction
end DeletionCode.PathMemory
