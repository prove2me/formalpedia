-- Prove2me | solution 1 for FixedOrderFactor.inv_q_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:01.083785+00:00
-- url     : https://prove2.me/submissions/e16daa27-6ef0-4a97-9e22-c0ab5c361826

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_inv_q_le_half

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (q : Nat.Primes) : 1 / (q : ℝ) < 1 :=
  lt_of_le_of_lt (inv_q_le_half q) (by norm_num)
end FixedOrderFactor
