-- Prove2me | solution 1 for ErdosPosa.deg_suppress
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:11.132593+00:00
-- url     : https://prove2.me/submissions/4af5b240-f0d8-4827-81d8-39883309b3c4

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
public import Theorems.Thm_ErdosPosa_suppress_adj
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
open Classical
namespace ErdosPosa
theorem _root_.solution [Finite V] {H : SimpleGraph V} {x a b : V} (hN : H.neighborSet x = {a, b})
    (hab : a ≠ b) (hnab : ¬ H.Adj a b) (v : V) :
    deg (suppress H x a b) v = if v = x then 0 else deg H v := by
  have hxa : H.Adj x a := by
    have : a ∈ H.neighborSet x := by rw [hN]; exact Set.mem_insert _ _
    exact this
  have hxb : H.Adj x b := by
    have : b ∈ H.neighborSet x := by rw [hN]; exact Set.mem_insert_of_mem _ rfl
    exact this
  have hxA : x ≠ a := hxa.ne
  have hxB : x ≠ b := hxb.ne
  by_cases hvx : v = x
  · subst hvx
    rw [if_pos rfl, deg, Set.ncard_eq_zero]
    ext w
    simp only [mem_neighborSet, suppress_adj, Set.mem_empty_iff_false, iff_false]
    rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h rfl
    · exact hxA h
    · exact hxB h
  simp only [hvx, ↓reduceIte]
  by_cases hva : v = a
  · subst hva
    have : (suppress H x v b).neighborSet v = insert b (H.neighborSet v \ {x}) := by
      ext w
      simp only [mem_neighborSet, suppress_adj, Set.mem_insert_iff, Set.mem_sdiff,
        Set.mem_singleton_iff]
      constructor
      · rintro (⟨h, -, h2⟩ | ⟨-, rfl, -⟩ | ⟨h, -⟩)
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl rfl
        · exact absurd h hab
      · rintro (rfl | ⟨h, h2⟩)
        · simp [hab]
        · exact Or.inl ⟨h, hvx, h2⟩
    rw [deg, deg, this, Set.ncard_insert_of_notMem, Set.ncard_sdiff_singleton_of_mem]
    · have : 0 < (H.neighborSet v).ncard :=
        Set.ncard_pos (Set.toFinite _) |>.2 ⟨x, hxa.symm⟩
      omega
    · exact hxa.symm
    · rintro ⟨h, -⟩; exact hnab h
  by_cases hvb : v = b
  · subst hvb
    have : (suppress H x a v).neighborSet v = insert a (H.neighborSet v \ {x}) := by
      ext w
      simp only [mem_neighborSet, suppress_adj, Set.mem_insert_iff, Set.mem_sdiff,
        Set.mem_singleton_iff]
      constructor
      · rintro (⟨h, -, h2⟩ | ⟨h, -⟩ | ⟨-, rfl, -⟩)
        · exact Or.inr ⟨h, h2⟩
        · exact absurd h.symm hab
        · exact Or.inl rfl
      · rintro (rfl | ⟨h, h2⟩)
        · simp [hab]
        · exact Or.inl ⟨h, hvx, h2⟩
    rw [deg, deg, this, Set.ncard_insert_of_notMem, Set.ncard_sdiff_singleton_of_mem]
    · have : 0 < (H.neighborSet v).ncard :=
        Set.ncard_pos (Set.toFinite _) |>.2 ⟨x, hxb.symm⟩
      omega
    · exact hxb.symm
    · rintro ⟨h, -⟩; exact hnab h.symm
  · rw [deg, deg]
    congr 1
    ext w
    simp only [mem_neighborSet, suppress_adj]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h hva
      · exact absurd h hvb
    · intro h
      refine Or.inl ⟨h, hvx, ?_⟩
      rintro rfl
      have : v ∈ H.neighborSet w := h.symm
      rw [hN] at this
      rcases this with h1 | h1
      · exact hva h1
      · exact hvb h1
end ErdosPosa
