-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.lengthen_seed_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:50.686833+00:00
-- url     : https://prove2.me/submissions/929fa2c9-7eef-4417-889b-c91bf370f51a

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_Windows_insertion_after
import Theorems.Thm_DeletionCode_Windows_insertion_before
import Theorems.Thm_DeletionCode_Windows_insertion_crossing


set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (p : Letters) (ell k : ℕ) (seed : Seed)
    (bit : Bool) (hseed : Agree p seed.offset seed.bits 0 k) :
    Agree (insertAt p ell bit) (lengthenSeed ell k seed bit).offset
      (lengthenSeed ell k seed bit).bits 0 k := by
  unfold lengthenSeed
  split_ifs with hbefore hafter
  · intro i hi
    exact (insertion_before p ell seed.offset k bit hbefore i hi).trans (hseed i hi)
  · intro i hi
    exact (insertion_after p ell seed.offset k bit hafter i hi).trans (hseed i hi)
  · have hs : seed.offset ≤ ell := by omega
    intro i hi
    have hx := insertion_crossing p ell seed.offset k bit hs i hi
    dsimp
    rw [Nat.zero_add]
    rw [hx]
    unfold insertionSeed
    split_ifs with hcut heq
    · simpa only [Nat.zero_add] using hseed i hi
    · rfl
    · simpa only [Nat.zero_add] using hseed (i - 1) (by omega)
end DeletionCode.HeaderRecovery
