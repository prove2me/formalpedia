-- Prove2me | solution 1 for DeletionCode.PartialWords.writeBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:08.574977+00:00
-- url     : https://prove2.me/submissions/7a7b3c5c-c891-4382-b68a-e1961ae1891b

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
import Theorems.Thm_DeletionCode_PartialWords_compatible_of_sound
import Theorems.Thm_DeletionCode_PartialWords_putBits_extends
import Theorems.Thm_DeletionCode_PartialWords_putBits_sound
import Theorems.Thm_DeletionCode_PartialWords_readBits_putBits
import Theorems.Thm_DeletionCode_PartialWords_writeBits_success

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by
  refine ⟨putBits s start bits,
    writeBits_success s p m start len hs hbound bits hbits,
    putBits_sound s p m start len hs bits hbits, ?_, readBits_putBits s start len bits⟩
  exact putBits_extends s start len bits
    (compatible_of_sound s p m start len hs hbound bits hbits)
end DeletionCode.PartialWords
