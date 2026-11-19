-- Prove2me | solution 1 for DeletionCode.SeedLookup.lookup_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:31.99133+00:00
-- url     : https://prove2.me/submissions/b44140c4-0512-448a-8458-f1ff9dca8e63

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
import Theorems.Thm_DeletionCode_SeedLookup_lookup_sound
import Theorems.Thm_DeletionCode_SeedLookup_lookup_exists
import Theorems.Thm_DeletionCode_SeedLookup_matches_unique

set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) :
    lookup x n k L r seed = some a ↔ Matches x n k L r seed a := by
  constructor
  · exact lookup_sound x n k L r a seed
  · intro ha
    obtain ⟨b, hb⟩ := lookup_exists x n k L r seed ⟨a, ha⟩
    have hab := matches_unique x n k L r a b seed hx ha
      (lookup_sound x n k L r b seed hb)
    simpa [hab] using hb
end DeletionCode.SeedLookup
