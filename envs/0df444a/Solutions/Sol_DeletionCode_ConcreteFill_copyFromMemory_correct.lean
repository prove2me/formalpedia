-- Prove2me | solution 1 for DeletionCode.ConcreteFill.copyFromMemory_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:36.15617+00:00
-- url     : https://prove2.me/submissions/a3b68d11-ef79-4de9-bd11-8db17fa27053

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
import Theorems.Thm_DeletionCode_PartialWords_readBits_sound
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords
namespace DeletionCode.ConcreteFill
theorem _root_.solution (source s : Memory) (q p : Letters)
    (sourceLength sourceStart len m start : ℕ) (bits : Bits len)
    (hsource : Sound source q sourceLength) (hs : Sound s p m)
    (hsourceBound : sourceStart + len ≤ sourceLength) (hbound : start + len ≤ m)
    (hread : readBits source sourceStart len = some bits)
    (hagree : Agree q sourceStart p start len) :
    ∃ t, copyFromMemory source sourceLength sourceStart len s m start = some t ∧
      Recovered s t p m start len := by
  have hbits : PartialWords.Matches bits p start := by
    intro i
    exact (readBits_sound source q sourceLength sourceStart len hsource
      hsourceBound bits hread i).trans (hagree i.val i.isLt)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start len hs hbound bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simp only [copyFromMemory, if_pos hsourceBound, hread, Option.bind_some]
    exact ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i
end DeletionCode.ConcreteFill
