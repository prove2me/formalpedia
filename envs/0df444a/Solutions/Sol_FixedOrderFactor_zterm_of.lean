-- Prove2me | solution 1 for FixedOrderFactor.zterm_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:37.829798+00:00
-- url     : https://prove2.me/submissions/9018de6b-2278-4c83-9904-d08ed6f480f7

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {N : Finset Nat.Primes} {s n : ℕ} (h0 : 0 < n) (h : PrimeTo N n) :
    zterm N s n = 1 / (n : ℝ) ^ s := by
  unfold zterm; rw [if_pos ⟨h0, h⟩]
end FixedOrderFactor
