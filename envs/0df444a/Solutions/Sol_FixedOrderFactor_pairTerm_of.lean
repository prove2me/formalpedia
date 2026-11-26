-- Prove2me | solution 1 for FixedOrderFactor.pairTerm_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:52.115038+00:00
-- url     : https://prove2.me/submissions/7f1ada76-688f-4863-9d12-aa98cb5875b2

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {N : Finset Nat.Primes} {r : ℕ} {ab : ℕ × ℕ}
    (h : 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2) :
    pairTerm N r ab = 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r := by
  unfold pairTerm; rw [if_pos h]
end FixedOrderFactor
