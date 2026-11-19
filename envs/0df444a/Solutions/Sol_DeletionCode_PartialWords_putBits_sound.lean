-- Prove2me | solution 1 for DeletionCode.PartialWords.putBits_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:34.338252+00:00
-- url     : https://prove2.me/submissions/9bc80c35-f321-45ed-86b8-5009fac90738

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (p : Letters) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by
  intro j hj b hb
  unfold putBits at hb
  split at hb
  · rename_i h
    have heq := Option.some.inj hb
    have hbit := hbits ⟨j - start, by omega⟩
    have hidx : start + (j - start) = j := by omega
    simpa [hidx, heq] using hbit
  · exact hs j hj b hb
end DeletionCode.PartialWords
