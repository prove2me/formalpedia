-- Prove2me | solution 1 for DeletionCode.ConcreteFill.fillFromBase_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:34.72485+00:00
-- url     : https://prove2.me/submissions/02140808-7595-45e9-819c-f68f2c59095d

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
import Theorems.Thm_DeletionCode_PartialWords_readBits_sound
import Theorems.Thm_DeletionCode_PartialWords_writeBits_correct
import Theorems.Thm_DeletionCode_SeedLookup_recoverWindow_of_occurrence


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords
namespace DeletionCode.ConcreteFill
theorem _root_.solution (x p : Letters) (n k L : ℕ)
    (s : Memory) (m start r : ℕ) (seed : Bits k)
    (hx : KUnique x n k) (hs : Sound s p m)
    (hbound : start + L ≤ m) (hr : r + k ≤ L)
    (hread : readBits s (start + r) k = some seed)
    (hocc : ∃ a, a + L ≤ n ∧ Agree x a p start L) :
    ∃ t, fillFromBase x n k L s m start r = some t ∧
      Recovered s t p m start L := by
  obtain ⟨a, ha, hagree⟩ := hocc
  have hseed : PartialWords.Matches seed p (start + r) :=
    readBits_sound s p m (start + r) k hs (by omega) seed hread
  have hlookup := SeedLookup.recoverWindow_of_occurrence
    x p n k L r a start seed hx hr ha hagree hseed
  let bits : Bits L := fun i => p (start + i.val)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start L hs hbound bits (fun _ => rfl)
  refine ⟨t, ?_, hsound, hext, hknown⟩
  simp only [fillFromBase, hread, Option.bind_some, hlookup]
  exact ht
end DeletionCode.ConcreteFill
