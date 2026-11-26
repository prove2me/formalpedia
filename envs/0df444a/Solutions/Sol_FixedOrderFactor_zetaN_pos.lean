-- Prove2me | solution 1 for FixedOrderFactor.zetaN_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:15.108088+00:00
-- url     : https://prove2.me/submissions/d2651d10-b03a-47d1-a76e-f8a61c8302c6

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_one_le_zetaN

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) : 0 < zetaN N s :=
  lt_of_lt_of_le one_pos (one_le_zetaN N hs)
end FixedOrderFactor
