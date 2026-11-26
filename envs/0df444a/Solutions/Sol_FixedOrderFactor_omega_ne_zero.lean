-- Prove2me | solution 1 for FixedOrderFactor.omega_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:29.96084+00:00
-- url     : https://prove2.me/submissions/7ffc57a1-eec6-43a4-8494-bc121b91c1ff

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) : ω r ≠ 0 := Complex.exp_ne_zero _
end FixedOrderFactor
