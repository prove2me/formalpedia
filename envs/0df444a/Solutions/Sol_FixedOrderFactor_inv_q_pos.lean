-- Prove2me | solution 1 for FixedOrderFactor.inv_q_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:24.2348+00:00
-- url     : https://prove2.me/submissions/5c326e35-1d73-4b55-8e69-5d7fafb93a47

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (q : Nat.Primes) : 0 < 1 / (q : ℝ) := by
  have := q.prop.pos; positivity
end FixedOrderFactor
