-- Prove2me | solution 1 for FixedOrderFactor.pairTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:57.35398+00:00
-- url     : https://prove2.me/submissions/a29fa4c3-27bb-493c-b0a8-5d3379ffb3b1

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) : 0 ≤ pairTerm N r ab := by
  unfold pairTerm; split_ifs <;> positivity
end FixedOrderFactor
