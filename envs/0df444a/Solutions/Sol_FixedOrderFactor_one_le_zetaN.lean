-- Prove2me | solution 1 for FixedOrderFactor.one_le_zetaN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:51.954428+00:00
-- url     : https://prove2.me/submissions/c1c36f7a-d1c7-4e3a-9db8-e3bcb039e02b

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_summable_zetaN_terms

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) : 1 ≤ zetaN N s := by
  have h := (summable_zetaN_terms N hs).le_tsum 1 (fun n _ => by split_ifs <;> positivity)
  simpa [primeTo_one, zetaN] using h
end FixedOrderFactor
