-- Prove2me | solution 1 for DenseTriangleFree.succ_mod_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:40.663329+00:00
-- url     : https://prove2.me/submissions/0d9cda16-77ec-4e4a-a74b-7fe06a76d288

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace DenseTriangleFree
theorem _root_.solution (i L : ℕ) (hL : 0 < L) :
    (i % L + 1 < L ∧ (i + 1) % L = i % L + 1) ∨ (i % L + 1 = L ∧ (i + 1) % L = 0) := by
  have hlt := Nat.mod_lt i hL
  have hdiv : (i + 1) % L = (i % L + 1) % L := by
    conv_lhs => rw [← Nat.div_add_mod i L, add_assoc, Nat.mul_add_mod]
  rcases (by omega : i % L + 1 < L ∨ i % L + 1 = L) with h | h
  · exact Or.inl ⟨h, by rw [hdiv, Nat.mod_eq_of_lt h]⟩
  · exact Or.inr ⟨h, by rw [hdiv, h, Nat.mod_self]⟩
end DenseTriangleFree
