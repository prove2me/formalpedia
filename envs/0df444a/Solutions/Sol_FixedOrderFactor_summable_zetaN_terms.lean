-- Prove2me | solution 1 for FixedOrderFactor.summable_zetaN_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:51:41.380865+00:00
-- url     : https://prove2.me/submissions/f74e0ca6-26d1-497c-9171-1a834a2ade45

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_fN_apply
public import Theorems.Thm_FixedOrderFactor_summable_fN

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0) := by
  exact (summable_fN N hs).of_norm.congr (fun n => fN_apply N _ n)
end FixedOrderFactor
