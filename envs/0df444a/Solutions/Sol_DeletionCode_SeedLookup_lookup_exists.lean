-- Prove2me | solution 1 for DeletionCode.SeedLookup.lookup_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:01.257841+00:00
-- url     : https://prove2.me/submissions/aa915260-dc76-4221-9bdd-9a3084ab6969

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup

set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (h : ∃ a, Matches x n k L r seed a) :
    ∃ a, lookup x n k L r seed = some a := by
  rcases h with ⟨a, ha⟩
  cases heq : lookup x n k L r seed with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp heq
    have hamem : a ∈ List.range (n + 1) := by
      simp only [List.mem_range]
      have := ha.2.1
      omega
    have hfalse := hnone a hamem
    exact False.elim (hfalse (decide_eq_true ha))
end DeletionCode.SeedLookup
