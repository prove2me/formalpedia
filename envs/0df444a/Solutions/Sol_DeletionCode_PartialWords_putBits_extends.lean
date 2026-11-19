-- Prove2me | solution 1 for DeletionCode.PartialWords.putBits_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:02:11.357893+00:00
-- url     : https://prove2.me/submissions/4963b283-9ffc-44db-8e6d-2c00ec1475c1

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (start len : ℕ) (bits : Bits len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by
  intro j b hb
  unfold putBits
  split
  · rename_i h
    let i : Fin len := ⟨j - start, by omega⟩
    have hi : start + i.val = j := by dsimp [i]; omega
    have hc' := hc i
    rw [hi, hb] at hc'
    rcases hc' with hn | heq
    · contradiction
    · simpa [i] using heq.symm
  · exact hb
end DeletionCode.PartialWords
