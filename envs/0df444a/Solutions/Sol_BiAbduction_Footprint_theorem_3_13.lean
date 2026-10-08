-- Prove2me | solution 1 for BiAbduction.Footprint.theorem_3_13
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T09:27:06.478393+00:00
-- url     : https://prove2.me/submissions/384b78ea-830c-4507-b067-1aaf4f4aff12

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

open BiAbduction.Footprint

private theorem heap_ext {h k : Heap} (hc : h.cell = k.cell) : h = k := by
  cases h
  cases k
  cases hc
  rfl

private theorem sub_refl (h : Heap) : Heap.Subheap h h := by
  intro l v hv
  exact hv

private theorem sub_trans {a b c : Heap} (hab : Heap.Subheap a b)
    (hbc : Heap.Subheap b c) : Heap.Subheap a c := by
  intro l v hv
  exact hbc l v (hab l v hv)

private theorem union_sub {h a b : Heap} (hu : Heap.IsUnion h a b) : Heap.Subheap a h := by
  intro l v hv
  simpa [hv] using hu.2 l

private theorem sub_split {a h : Heap} (ha : Heap.Subheap a h) :
    ∃ b, Heap.IsUnion h a b := by
  classical
  let b : Heap := {
    cell := fun l => if a.cell l = none then h.cell l else none
    nil_unalloc := by simp [a.nil_unalloc, h.nil_unalloc]
    finite_dom := h.finite_dom.subset (by
      intro l hl
      simp only [Set.mem_setOf_eq] at hl ⊢
      by_contra hn
      simp [hn] at hl) }
  refine ⟨b, ?_, ?_⟩
  · intro l
    by_cases hn : a.cell l = none
    · exact Or.inl hn
    · exact Or.inr (by simp [b, hn])
  · intro l
    cases he : a.cell l with
    | none => simp [b, he]
    | some v => simp [b, he, ha l v he]

private theorem spatial_iff (A B : Pred) :
    SpatialLe A B ↔ ∀ p ∈ B, ∃ a : Heap, Heap.Subheap a p.2 ∧ (p.1, a) ∈ A := by
  constructor
  · intro hab p hp
    obtain ⟨a, b, hu, hm, _⟩ := hab hp
    exact ⟨a, union_sub hu, hm⟩
  · intro hab p hp
    obtain ⟨a, ha, hm⟩ := hab p hp
    obtain ⟨b, hu⟩ := sub_split ha
    exact ⟨a, b, hu, hm, Set.mem_univ _⟩

private theorem spatial_trans {A B C : Pred} (hab : SpatialLe A B)
    (hbc : SpatialLe B C) : SpatialLe A C := by
  rw [spatial_iff] at hab hbc ⊢
  intro p hp
  obtain ⟨b, hb, hm⟩ := hbc p hp
  obtain ⟨a, ha, ham⟩ := hab (p.1, b) hm
  exact ⟨a, sub_trans ha hb, ham⟩

private theorem sub_card_eq {a b : Heap} (hab : Heap.Subheap a b)
    (hc : {l | b.cell l ≠ none}.ncard ≤ {l | a.cell l ≠ none}.ncard) : a = b := by
  have hs : {l | a.cell l ≠ none} ⊆ {l | b.cell l ≠ none} := by
    intro l hl
    cases he : a.cell l with
    | none => exact False.elim (hl he)
    | some v => simp [hab l v he]
  have hd := Set.eq_of_subset_of_ncard_le hs hc b.finite_dom
  apply heap_ext
  funext l
  cases he : a.cell l with
  | some v => exact (hab l v he).symm
  | none =>
    have hn : b.cell l = none := by
      by_contra hb
      have : l ∈ {l | a.cell l ≠ none} := hd.symm ▸ hb
      exact this he
    exact hn.symm

private theorem min_spatial (A : Pred) : SpatialLe (minSet A) A := by
  classical
  rw [spatial_iff]
  intro p hp
  let size : Heap → ℕ := fun h => {l | h.cell l ≠ none}.ncard
  obtain ⟨a, ha, hleast⟩ := (measure size).wf.has_min
    {h : Heap | Heap.Subheap h p.2 ∧ (p.1, h) ∈ A} ⟨p.2, sub_refl p.2, hp⟩
  refine ⟨a, ha.1, ha.2, ?_⟩
  intro b hb hbm
  apply sub_card_eq hb
  exact Nat.le_of_not_lt (hleast b ⟨sub_trans hb ha.1, hbm⟩)

private theorem minimal_least (F G A : Pred) (hsol : IsSolution F G A)
    (hle : ∀ M, IsSolution F G M → SpatialLe A M) :
    IsLeastSolution F G (minSet A) := by
  have hm : IsSolution F G (minSet A) := by
    intro p hp
    obtain ⟨a, b, hu, ha, hb⟩ := hp
    exact hsol ⟨a, b, hu, ha, hb.1⟩
  refine ⟨hm, ?_⟩
  intro M hM
  have hl : SpatialLe (minSet A) M := spatial_trans (min_spatial A) (hle M hM)
  by_cases hr : SpatialLe M (minSet A)
  · refine Or.inr ⟨hl, hr, ?_⟩
    intro p hp
    obtain ⟨b, hb, hbm⟩ := (spatial_iff _ _).mp hr p hp
    obtain ⟨a, ha, ham⟩ := (spatial_iff _ _).mp (hle M hM) (p.1, b) hbm
    have hae : a = p.2 := hp.2 a (sub_trans ha hb) ham
    have hbe : b = p.2 := by
      apply sub_card_eq hb
      apply Set.ncard_le_ncard _ b.finite_dom
      intro l hlp
      cases he : p.2.cell l with
      | none => exact False.elim (hlp he)
      | some v =>
        have : b.cell l = some v := ha l v (hae.symm ▸ he)
        simp [this]
    simpa [hbe] using hbm
  · exact Or.inl ⟨hl, hr⟩

private theorem union_swap {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.IsUnion h b a := by
  refine ⟨fun l => (hu.1 l).symm, ?_⟩
  intro l
  rcases hu.1 l with ha | hb
  · simp [hu.2 l, ha]
  · simp [hu.2 l, hb]

private theorem solution_iff (F G A : Pred) : IsSolution F G A ↔ A ⊆ wand F G := by
  constructor
  · intro hs p hp h hu hh hf
    exact hs ⟨h, p.2, union_swap hh, hf, hp⟩
  · intro hs p hp
    obtain ⟨a, b, hu, ha, hb⟩ := hp
    exact hs hb a p.2 (union_swap hu) ha

theorem solution (F G : Pred) :
    IsLeastSolution F G (minSet (wand F G)) ∧
    ∀ M : Pred, IsLeastSolution F G M → M = minSet (wand F G) := by
  have hw : IsLeastSolution F G (minSet (wand F G)) := by
    apply minimal_least
    · exact (solution_iff _ _ _).mpr (Set.Subset.refl _)
    · intro M hm
      rw [spatial_iff]
      intro p hp
      exact ⟨p.2, sub_refl p.2, (solution_iff _ _ _).mp hm hp⟩
  refine ⟨hw, ?_⟩
  intro M hm
  have h₁ := hw.2 M hm.1
  have h₂ := hm.2 _ hw.1
  have hinc : Entails M (minSet (wand F G)) ∧ Entails (minSet (wand F G)) M := by
    unfold Better at h₁ h₂
    tauto
  exact Set.Subset.antisymm hinc.1 hinc.2

#print axioms solution
