-- Prove2me | solution 1 for Erdos919.rows_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:39:05.996181+00:00
-- url     : https://prove2.me/submissions/1dc4dc8e-8a06-4c00-8a1d-a2a6cf33faea

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_exists_embedding_of_unbounded

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (X : Set (W.{u} ×ₗ W.{u})) (hX : typeLT X < typeLT (W.{u} ×ₗ W.{u})) :
    ∃ ξ₀ : W.{u}, ∀ ξ, (∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X) → ξ < ξ₀ := by
  by_contra hcon
  push Not at hcon
  let F : Set W.{u} := {ξ | ∀ x, ∃ η, x ≤ η ∧ toLex (ξ, η) ∈ X}
  obtain ⟨eF⟩ := exists_embedding_of_unbounded F (fun x => by
    obtain ⟨ξ, hξ, hx⟩ := hcon x
    exact ⟨ξ, hξ, hx⟩)
  have hrow : ∀ ξ : F, Nonempty (W.{u} ↪o {η : W.{u} | toLex (ξ.1, η) ∈ X}) := fun ξ =>
    exists_embedding_of_unbounded _ (fun x => by
      obtain ⟨η, h1, h2⟩ := ξ.2 x
      exact ⟨η, h2, h1⟩)
  let eR : ∀ ξ : F, W.{u} ↪o {η : W.{u} | toLex (ξ.1, η) ∈ X} :=
    fun ξ => Classical.choice (hrow ξ)
  let φ : W.{u} → W.{u} → X := fun i j => ⟨toLex ((eF i).1, (eR (eF i) j).1), (eR (eF i) j).2⟩
  have hφ : ∀ i j i' j', (i < i' ∨ i = i' ∧ j < j') → φ i j < φ i' j' := by
    intro i j i' j' h
    show toLex ((eF i).1, (eR (eF i) j).1) < toLex ((eF i').1, (eR (eF i') j').1)
    rw [Prod.Lex.toLex_lt_toLex]
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (eF.strictMono h)
    · exact Or.inr ⟨rfl, (eR (eF i)).strictMono h⟩
  let Φ : W.{u} ×ₗ W.{u} → X := fun p => φ (ofLex p).1 (ofLex p).2
  have hΦ : StrictMono Φ := by
    intro p q hpq
    exact hφ _ _ _ _ (Prod.Lex.lt_iff.1 hpq)
  have hle : typeLT (W.{u} ×ₗ W.{u}) ≤ typeLT X :=
    type_le_iff'.2 ⟨(OrderEmbedding.ofStrictMono Φ hΦ).ltEmbedding⟩
  exact absurd hX (not_lt.2 hle)
end Erdos919
