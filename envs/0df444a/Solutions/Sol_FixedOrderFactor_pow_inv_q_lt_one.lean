-- Prove2me | solution 1 for FixedOrderFactor.pow_inv_q_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:21.174782+00:00
-- url     : https://prove2.me/submissions/1bf41db8-2f72-4ede-a15a-2fcb4873e3a7

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_inv_q_pos
public import Theorems.Thm_FixedOrderFactor_inv_q_lt_one

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (q : Nat.Primes) {s : ℕ} (hs : s ≠ 0) : (1 / (q : ℝ)) ^ s < 1 :=
  pow_lt_one₀ (inv_q_pos q).le (inv_q_lt_one q) hs
end FixedOrderFactor
