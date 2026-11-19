-- Prove2me | solution 1 for DeletionCode.PartialWords.compatible_of_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:02:08.183284+00:00
-- url     : https://prove2.me/submissions/0e1247d2-0a85-48dd-afaf-64eb84202aed

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    Compatible s start bits := by
  intro i
  cases h : s (start + i.val) with
  | none => exact Or.inl rfl
  | some b =>
    have hb := hs (start + i.val) (by have := i.isLt; omega) b h
    exact Or.inr (congrArg some (hb.trans (hbits i).symm))
end DeletionCode.PartialWords
