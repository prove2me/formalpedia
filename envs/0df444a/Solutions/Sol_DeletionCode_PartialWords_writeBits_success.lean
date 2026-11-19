-- Prove2me | solution 1 for DeletionCode.PartialWords.writeBits_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:35.212038+00:00
-- url     : https://prove2.me/submissions/48614560-7c83-47d6-ab84-3cba0b76bbff

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
import Theorems.Thm_DeletionCode_PartialWords_compatible_of_sound

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by
  simp [writeBits, hbound, compatible_of_sound s p m start len hs hbound bits hbits]
end DeletionCode.PartialWords
