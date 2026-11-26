-- Prove2me | solution 1 for FixedOrderFactor.mem_primesUpTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:16.579115+00:00
-- url     : https://prove2.me/submissions/72d40b02-af6e-499b-9fea-629ef11e5f31

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) (Y : ℕ) (q : Nat.Primes) :
    q ∈ primesUpTo N Y ↔ (q : ℕ) ≤ Y ∧ q ∉ N := by
  rw [primesUpTo, Finset.mem_filter]
  have : q ∈ (Finset.range (Y + 1)).preimage (fun q : Nat.Primes => (q : ℕ))
      Nat.Primes.coe_nat_injective.injOn ↔ (q : ℕ) ∈ Finset.range (Y + 1) :=
    Finset.mem_preimage
  rw [this, Finset.mem_range]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩
end FixedOrderFactor
