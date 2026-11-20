-- Prove2me | solution 1 for DeletionCode.RecordPacking.unpack_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:29.880823+00:00
-- url     : https://prove2.me/submissions/3061d51c-7fa5-4700-a8d7-3ec9177bcbe5

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_RecordPacking
import Theorems.Thm_DeletionCode_RecordPacking_unpack_of_positions

set_option autoImplicit true
open DeletionCode DeletionCode.RecordPacking
variable {α β : Type*}
namespace DeletionCode.RecordPacking
theorem _root_.solution (decode : β → Option (Option α)) (encode : α → β)
    (padding : β) (hpadding : decode padding = some none)
    (xs : List α) (hencode : ∀ a ∈ xs, decode (encode a) = some (some a))
    (size : ℕ) (hsize : xs.length ≤ size) :
    unpack decode size (pack padding (xs.map encode) size) = some xs := by
  apply unpack_of_positions decode size _ xs hsize
  intro i
  unfold pack
  cases hget : xs[i.val]? with
  | none => simpa [List.getElem?_map, hget] using hpadding
  | some a =>
    have ha : a ∈ xs := List.mem_of_getElem? hget
    simpa [List.getElem?_map, hget] using hencode a ha
end DeletionCode.RecordPacking
