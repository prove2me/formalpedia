-- Prove2me | solution 1 for DeletionCode.PartialWords.readBits_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:07:26.376962+00:00
-- url     : https://prove2.me/submissions/0ffa1d67-3702-4f97-a608-d67b9758768c

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords
import Theorems.Thm_DeletionCode_PartialWords_readBits_eq_some_iff

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits len) (hread : readBits s start len = some bits) :
    Matches bits p start := by
  intro i
  exact hs (start + i.val) (by have := i.isLt; omega) (bits i)
    ((readBits_eq_some_iff s start len bits).mp hread i)
end DeletionCode.PartialWords
