-- Prove2me | solution 1 for DeletionCode.PartialWords.readBits_putBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:37.454212+00:00
-- url     : https://prove2.me/submissions/9bd818ed-d6d8-4ab1-92fa-b46ed4b44798

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
import Theorems.Thm_DeletionCode_PartialWords_readBits_eq_some_iff
import Theorems.Thm_DeletionCode_PartialWords_putBits_at

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits (putBits s start bits) start len = some bits := by
  apply (readBits_eq_some_iff _ _ _ _).mpr
  exact putBits_at s start len bits
end DeletionCode.PartialWords
