-- Prove2me | solution 1 for FixedOrderFactor.zterm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:18.072168+00:00
-- url     : https://prove2.me/submissions/b2771970-54be-495c-ae9b-3ed401238ca8

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {N : Finset Nat.Primes} {s n : ℕ} (h : zterm N s n ≠ 0) :
    0 < n ∧ PrimeTo N n := by
  unfold zterm at h; split_ifs at h with h'; exacts [h', absurd rfl h]
end FixedOrderFactor
