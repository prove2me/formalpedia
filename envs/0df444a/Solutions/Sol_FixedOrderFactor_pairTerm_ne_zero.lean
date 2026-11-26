-- Prove2me | solution 1 for FixedOrderFactor.pairTerm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:36.127286+00:00
-- url     : https://prove2.me/submissions/db820c06-c0ca-4c6a-bd6d-ab946ee1797a

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ} (h : pairTerm N r ab ≠ 0) :
    0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2 := by
  unfold pairTerm at h; split_ifs at h with h'; exacts [h', absurd rfl h]
end FixedOrderFactor
