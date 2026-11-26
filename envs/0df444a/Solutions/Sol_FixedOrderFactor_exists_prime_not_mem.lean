-- Prove2me | solution 1 for FixedOrderFactor.exists_prime_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:51:18.755164+00:00
-- url     : https://prove2.me/submissions/15916f2c-aee6-4b88-87ec-33961b115de0

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) : ∃ q : Nat.Primes, q ∉ N := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes ((N.sup (fun q => (q : ℕ))) + 1)
  refine ⟨⟨p, hp2⟩, fun h => ?_⟩
  have := Finset.le_sup (f := fun q : Nat.Primes => (q : ℕ)) h
  simp at this; omega
end FixedOrderFactor
