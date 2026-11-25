-- Prove2me | solution 1 for ErdosPosa.suppress_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:16.671542+00:00
-- url     : https://prove2.me/submissions/3b32d4a7-d28b-4f71-aef3-66752b534be9

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {H : SimpleGraph V} {x a b u w : V} :
    (suppress H x a b).Adj u w ↔
      (H.Adj u w ∧ u ≠ x ∧ w ≠ x) ∨ (u = a ∧ w = b ∧ a ≠ b) ∨ (u = b ∧ w = a ∧ a ≠ b) := by
  simp only [suppress, fromRel_adj]
  constructor
  · rintro ⟨hne, (⟨h, h1, h2⟩ | ⟨rfl, rfl⟩) | (⟨h, h1, h2⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨h, h1, h2⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, hne⟩)
    · exact Or.inl ⟨h.symm, h2, h1⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl, fun h => hne h.symm⟩)
  · rintro (⟨h, h1, h2⟩ | ⟨rfl, rfl, hne⟩ | ⟨rfl, rfl, hne⟩)
    · exact ⟨h.ne, Or.inl (Or.inl ⟨h, h1, h2⟩)⟩
    · exact ⟨hne, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ⟨fun h => hne h.symm, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
end ErdosPosa
