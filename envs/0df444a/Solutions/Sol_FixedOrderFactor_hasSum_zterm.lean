-- Prove2me | solution 1 for FixedOrderFactor.hasSum_zterm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:48.576031+00:00
-- url     : https://prove2.me/submissions/d3288324-cf2c-4c2b-a44a-197c4e4df2dd

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
public import Theorems.Thm_FixedOrderFactor_summable_zetaN_terms


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasSum (zterm N s) (zetaN N s) :=
  (summable_zetaN_terms N hs).hasSum
end FixedOrderFactor
