-- Prove2me | solution 1 for DeletionCode.PartialWords.writeBits_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:54.68938+00:00
-- url     : https://prove2.me/submissions/7e7f3569-df54-4db8-bed2-7c03fa836c79

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
import Theorems.Thm_DeletionCode_PartialWords_putBits_extends

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s t : Memory) (m start len : ℕ) (bits : Bits len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by
  unfold writeBits at hwrite
  split at hwrite
  · rename_i h
    cases Option.some.inj hwrite
    exact putBits_extends s start len bits h.2
  · contradiction
end DeletionCode.PartialWords
