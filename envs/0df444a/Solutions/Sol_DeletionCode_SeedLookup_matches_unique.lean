-- Prove2me | solution 1 for DeletionCode.SeedLookup.matches_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:02.93841+00:00
-- url     : https://prove2.me/submissions/0bb15101-938d-4f89-b173-ddbd3c41ad78

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
import Theorems.Thm_DeletionCode_Windows_unique_window_lookup


set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution (x : Letters) (n k L r a b : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (ha : Matches x n k L r seed a)
    (hb : Matches x n k L r seed b) : a = b := by
  apply unique_window_lookup x n k L a b r hx ha.2.1 hb.2.1 ha.1
  intro i hi
  exact (ha.2.2 ⟨i, hi⟩).trans (hb.2.2 ⟨i, hi⟩).symm
end DeletionCode.SeedLookup
