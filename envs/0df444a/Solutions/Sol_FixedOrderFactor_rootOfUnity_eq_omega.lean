-- Prove2me | solution 1 for FixedOrderFactor.rootOfUnity_eq_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:57.943148+00:00
-- url     : https://prove2.me/submissions/9da8ac6b-2eec-4a40-b723-8693ecb33c10

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
theorem _root_.solution (r j : ℕ) : rootOfUnity r j = ω r ^ j := by
  rw [rootOfUnity, ω, ← Complex.exp_nat_mul]; congr 1; ring
end FixedOrderFactor
