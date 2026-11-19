-- Prove2me | solution 1 for DeletionCode.PartialWords.putBits_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:07.254865+00:00
-- url     : https://prove2.me/submissions/4cb6c922-e0a2-44d8-a623-e7df6a8a451f

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (start len : ℕ) (bits : Bits len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by
  simp [putBits, i.isLt]
end DeletionCode.PartialWords
