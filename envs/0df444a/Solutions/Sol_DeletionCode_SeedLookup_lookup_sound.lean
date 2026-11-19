-- Prove2me | solution 1 for DeletionCode.SeedLookup.lookup_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:02:48.206202+00:00
-- url     : https://prove2.me/submissions/cea63e58-9626-4af4-bbc2-6c435e2a09ed

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup

set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution (x : Letters) (n k L r a : ℕ) (seed : Fin k → Bool)
    (h : lookup x n k L r seed = some a) : Matches x n k L r seed a := by
  have hp : decide (Matches x n k L r seed a) = true :=
    List.find?_some (p := fun b => decide (Matches x n k L r seed b)) h
  exact of_decide_eq_true hp
end DeletionCode.SeedLookup
