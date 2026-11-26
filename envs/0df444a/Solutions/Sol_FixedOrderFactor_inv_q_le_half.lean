-- Prove2me | solution 1 for FixedOrderFactor.inv_q_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:00.144261+00:00
-- url     : https://prove2.me/submissions/45a563ff-f06c-4b8b-b3e2-feb89fac89e1

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (q : Nat.Primes) : 1 / (q : ℝ) ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast q.prop.two_le
  exact one_div_le_one_div_of_le (by norm_num) this
end FixedOrderFactor
