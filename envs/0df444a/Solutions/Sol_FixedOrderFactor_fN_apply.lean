-- Prove2me | solution 1 for FixedOrderFactor.fN_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:42.104544+00:00
-- url     : https://prove2.me/submissions/2e535278-e1a7-4d07-b7c0-59745231d56b

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) (n : ℕ) :
    fN N s hs n = if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0 := by
  show (if PrimeTo N n then 1 / (n : ℝ) ^ s else 0) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs]
  · simp [hn]
end FixedOrderFactor
