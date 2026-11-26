-- Prove2me | solution 1 for FixedOrderFactor.pairTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:54.096365+00:00
-- url     : https://prove2.me/submissions/69d025d6-1006-4e19-a8f1-b92cf51d5e32

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
public import Theorems.Thm_FixedOrderFactor_zterm_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) :
    pairTerm N r ab ≤ zterm N r ab.1 * zterm N r ab.2 := by
  unfold pairTerm zterm
  by_cases h : 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
  · rw [if_pos h, if_pos ⟨h.1, h.2.2.2.1⟩, if_pos ⟨h.2.1, h.2.2.2.2⟩]
    push_cast; rw [mul_pow]; field_simp; rfl
  · rw [if_neg h]; exact mul_nonneg (zterm_nonneg N r _) (zterm_nonneg N r _)
end FixedOrderFactor
