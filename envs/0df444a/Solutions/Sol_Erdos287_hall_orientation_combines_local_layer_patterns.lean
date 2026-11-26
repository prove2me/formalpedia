-- Prove2me | solution 1 for Erdos287.hall_orientation_combines_local_layer_patterns
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:46:30.512315+00:00
-- url     : https://prove2.me/submissions/bd4d67a6-9138-475d-bc09-851a5b05745a

import Mathlib

open Finset

set_option autoImplicit false

/-- If each individual interface can be retained and the adjacency edges
can be assigned to distinct incident layers, whole allowed layer patterns
can be chosen without leaving an uncovered edge. -/
theorem solution (P E : Finset ℕ) (left right posL posR : ℕ → ℕ)
    (F : ℕ → Finset (Finset ℕ))
    (hP : ∀ p ∈ P, (F p).Nonempty)
    (hE : ∀ e ∈ E, left e ∈ P ∧ right e ∈ P)
    (hL : ∀ e ∈ E, ∃ T ∈ F (left e), posL e ∈ T)
    (hR : ∀ e ∈ E, ∃ T ∈ F (right e), posR e ∈ T)
    (hHall : ∀ S ⊆ E, S.card ≤ ((S.image left) ∪ S.image right).card) :
    ∃ C : ℕ → Finset ℕ, (∀ p ∈ P, C p ∈ F p) ∧
      ∀ e ∈ E, posL e ∈ C (left e) ∨ posR e ∈ C (right e) := by
  classical
  let N (e : ↥E) : Finset ℕ := {left e.val, right e.val}
  have hmatch (S : Finset ↥E) : S.card ≤ (S.biUnion N).card := by
    let J := S.image (fun e : ↥E => e.val)
    have hJ : J ⊆ E := by
      intro e he
      obtain ⟨q, _, rfl⟩ := mem_image.mp he
      exact q.property
    have hu : (J.image left ∪ J.image right) = S.biUnion N := by
      ext p
      constructor
      · intro hp
        rcases mem_union.mp hp with h | h
        · obtain ⟨e, he, rfl⟩ := mem_image.mp h
          obtain ⟨q, hq, rfl⟩ := mem_image.mp he
          exact mem_biUnion.mpr ⟨q, hq, by simp [N]⟩
        · obtain ⟨e, he, rfl⟩ := mem_image.mp h
          obtain ⟨q, hq, rfl⟩ := mem_image.mp he
          exact mem_biUnion.mpr ⟨q, hq, by simp [N]⟩
      · intro hp
        obtain ⟨e, he, hp⟩ := mem_biUnion.mp hp
        have hj : e.val ∈ J := mem_image_of_mem _ he
        rcases (show p = left e.val ∨ p = right e.val by simpa [N] using hp) with rfl | rfl
        · exact mem_union_left _ (mem_image_of_mem _ hj)
        · exact mem_union_right _ (mem_image_of_mem _ hj)
    have hc : J.card = S.card := card_image_of_injective _ Subtype.val_injective
    rw [← hu, ← hc]
    exact hHall J hJ
  obtain ⟨f, hf, hfn⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hmatch
  let need (e : ↥E) := if f e = left e.val then posL e.val else posR e.val
  have hfside (e : ↥E) : f e = left e.val ∨ f e = right e.val := by
    simpa [N] using hfn e
  have hNeed (e : ↥E) : ∃ T ∈ F (f e), need e ∈ T := by
    by_cases hl : f e = left e.val
    · simpa only [need, if_pos hl, hl] using hL e.val e.property
    · have hr := (hfside e).resolve_left hl
      simpa only [need, if_neg hl, hr] using hR e.val e.property
  have hlocal (p : ℕ) (hp : p ∈ P) :
      ∃ T ∈ F p, ∀ e : ↥E, f e = p → need e ∈ T := by
    by_cases h : ∃ e : ↥E, f e = p
    · obtain ⟨e, he⟩ := h
      obtain ⟨T, ht, hn⟩ := hNeed e
      refine ⟨T, he ▸ ht, ?_⟩
      intro e' he'
      have heq : e' = e := hf (he'.trans he.symm)
      simpa only [heq] using hn
    · obtain ⟨T, ht⟩ := hP p hp
      exact ⟨T, ht, fun e he => (h ⟨e, he⟩).elim⟩
  choose C hC hcover using hlocal
  let sel (p : ℕ) : Finset ℕ := if hp : p ∈ P then C p hp else ∅
  refine ⟨sel, fun p hp => by simpa only [sel, dif_pos hp] using hC p hp, ?_⟩
  intro e he
  let e' : ↥E := ⟨e, he⟩
  by_cases hl : f e' = left e
  · left
    have hmem := hcover (left e) (hE e he).1 e' hl
    simpa only [need, e', hl, if_true, sel, dif_pos (hE e he).1] using hmem
  · right
    have hr : f e' = right e := (hfside e').resolve_left hl
    have hmem := hcover (right e) (hE e he).2 e' hr
    simpa only [need, e', if_neg hl, sel, dif_pos (hE e he).2] using hmem

