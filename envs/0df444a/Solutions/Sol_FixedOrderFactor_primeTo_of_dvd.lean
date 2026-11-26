-- Prove2me | solution 1 for FixedOrderFactor.primeTo_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:49.548821+00:00
-- url     : https://prove2.me/submissions/d6077169-765c-499b-81c6-eca791fa2e95

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {N : Finset Nat.Primes} {m n : ℕ} (h : PrimeTo N n) (hmn : m ∣ n) :
    PrimeTo N m := fun q hq hqm => h q hq (hqm.trans hmn)
end FixedOrderFactor
