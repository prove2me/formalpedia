-- Prove2me | solution 1 for FixedOrderFactor.rootOfUnity_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:43.485945+00:00
-- url     : https://prove2.me/submissions/86899a89-f4c5-4745-ae0a-63020b2308b3

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r j : ℕ) : rootOfUnity r j = Complex.exp (2 * π * I / r) ^ j := by
  rw [rootOfUnity, ← Complex.exp_nat_mul]; congr 1; ring
end FixedOrderFactor
