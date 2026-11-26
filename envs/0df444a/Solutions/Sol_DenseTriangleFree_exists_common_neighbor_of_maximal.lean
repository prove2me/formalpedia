-- Prove2me | solution 1 for DenseTriangleFree.exists_common_neighbor_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:16.708853+00:00
-- url     : https://prove2.me/submissions/4d2f91db-641b-43d5-a24c-52eb8f5bb806

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Maximal
public import Theorems.Thm_DenseTriangleFree_triangle_of_cliqueFree


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*}
namespace DenseTriangleFree
theorem _root_.solution {G : SimpleGraph V}
    (hG : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G) {u v : V} (huv : u ≠ v)
    (hnadj : ¬ G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj v w := by
  classical
  by_contra hno
  push Not at hno
  have hadj : ∀ x y, (G ⊔ edge u v).Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h
    rcases (sup_adj _ _ _ _).mp h with h | h
    · exact Or.inl h
    · rw [edge_adj] at h
      tauto
  have hfree : (G ⊔ edge u v).CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
    have hab' := (G ⊔ edge u v).ne_of_adj hab
    have hac' := (G ⊔ edge u v).ne_of_adj hac
    have hbc' := (G ⊔ edge u v).ne_of_adj hbc
    rcases hadj _ _ hab with h1 | ⟨e1, e1'⟩ | ⟨e1, e1'⟩ <;>
    rcases hadj _ _ hac with h2 | ⟨e2, e2'⟩ | ⟨e2, e2'⟩ <;>
    rcases hadj _ _ hbc with h3 | ⟨e3, e3'⟩ | ⟨e3, e3'⟩ <;>
    subst_vars <;>
    first
      | exact triangle_of_cliqueFree hG.prop h1 h3 h2
      | exact hab' rfl | exact hac' rfl | exact hbc' rfl | exact huv rfl
      | exact hnadj ‹_› | exact hnadj (G.adj_symm ‹_›)
      | exact hno _ ‹_› ‹_›
      | exact hno _ ‹_› (G.adj_symm ‹_›)
      | exact hno _ (G.adj_symm ‹_›) ‹_›
      | exact hno _ (G.adj_symm ‹_›) (G.adj_symm ‹_›)
  have hle : G ⊔ edge u v ≤ G := hG.le_of_ge hfree le_sup_left
  exact hnadj (hle (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)))
end DenseTriangleFree
