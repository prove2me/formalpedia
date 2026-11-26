-- Prove2me | solution 1 for FixedOrderFactor.zetaN_eq_tsum_fN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:53.38974+00:00
-- url     : https://prove2.me/submissions/5480efee-fe35-43f6-8d87-c5a7ede54a01

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_fN_apply

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) :
    zetaN N s = ∑' n, fN N s hs n := by
  simp only [zetaN, fN_apply]
end FixedOrderFactor
