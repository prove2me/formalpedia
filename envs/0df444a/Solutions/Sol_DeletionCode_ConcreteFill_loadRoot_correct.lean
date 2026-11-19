-- Prove2me | solution 1 for DeletionCode.ConcreteFill.loadRoot_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:57.769192+00:00
-- url     : https://prove2.me/submissions/94f966ea-6ff3-4561-928d-f79c9a803ac3

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords
namespace DeletionCode.ConcreteFill
theorem _root_.solution (x p : Letters) (n a len : ℕ) (s : Memory) (m : ℕ)
    (hs : Sound s p m) (ha : a + len ≤ n) (hbound : len ≤ m)
    (hocc : Agree x a p 0 len) :
    ∃ t, loadRoot x n a len s m = some t ∧ Recovered s t p m 0 len := by
  let bits : Bits len := fun i => x (a + i.val)
  have hbits : PartialWords.Matches bits p 0 := fun i => hocc i.val i.isLt
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m 0 len hs (by omega) bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [loadRoot, if_pos ha] using ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i
end DeletionCode.ConcreteFill
