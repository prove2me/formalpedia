-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.shorten_seed_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:47.752072+00:00
-- url     : https://prove2.me/submissions/984a106f-90a9-45d3-aab7-94a3630c30ea

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_Windows_deletion_after
import Theorems.Thm_DeletionCode_Windows_deletion_before
import Theorems.Thm_DeletionCode_Windows_deletion_crossing


set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (p : Letters) (ell k : ℕ) (seed : Seed)
    (extra : Bool) (hseed : Agree p seed.offset seed.bits 0 k)
    (hextra : seed.offset ≤ ell → ell < seed.offset + k →
      extra = deleteAt p ell (seed.offset + k - 1)) :
    Agree (deleteAt p ell) (shortenSeed ell k seed extra).offset
      (shortenSeed ell k seed extra).bits 0 k := by
  unfold shortenSeed
  split_ifs with hbefore hafter
  · intro i hi
    exact (deletion_before p ell seed.offset k hbefore i hi).trans (hseed i hi)
  · intro i hi
    exact (deletion_after p ell seed.offset k hafter i hi).trans (hseed i hi)
  · have hs : seed.offset ≤ ell := by omega
    have he : ell < seed.offset + k := by omega
    intro i hi
    have hx := deletion_crossing p ell seed.offset k hs he i hi
    dsimp
    rw [Nat.zero_add]
    rw [hx]
    unfold deletionSeed
    split_ifs with hcut hlast
    · simpa only [Nat.zero_add] using hseed i hi
    · simpa only [Nat.zero_add] using hseed (i + 1) hlast
    · exact (hextra hs he).symm
end DeletionCode.HeaderRecovery
