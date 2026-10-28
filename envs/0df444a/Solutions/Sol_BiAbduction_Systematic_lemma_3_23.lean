-- Prove2me | solution 1 for BiAbduction.Systematic.lemma_3_23
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T03:29:20.686993+00:00
-- url     : https://prove2.me/submissions/e0de0ec5-2169-4072-a676-69fe9007508d

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Semantics

open BiAbduction.Systematic

namespace SolBiAbductionLemma323

private theorem heap_ext {h k : Heap} (hc : h.cell = k.cell) : h = k := by
  cases h
  cases k
  cases hc
  rfl

private theorem union_swap {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.IsUnion h b a := by
  refine ⟨fun l => (hu.1 l).symm, ?_⟩
  intro l
  rcases hu.1 l with ha | hb
  · simp [hu.2 l, ha]
  · simp [hu.2 l, hb]

private theorem union_sub_right {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.Subheap b h := by
  intro l v hv
  have hdisj := hu.1 l
  have hcell := hu.2 l
  rcases hdisj with ha | hb
  · simp [ha, hv] at hcell
    exact hcell
  · simp [hb] at hv

private theorem sub_split {a h : Heap} (ha : Heap.Subheap a h) :
    ∃ b, Heap.IsUnion h b a := by
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
    · exact Or.inr hn
    · exact Or.inl (by simp [b, hn])
  · intro l
    cases he : a.cell l with
    | none => simp [b, he]
    | some v => simp [b, he, ha l v he]

private theorem mem_sepConj_emp_compl_iff (G : Pred) (p : State) :
    p ∈ sepConj empᶜ G ↔
      ∃ h' : Heap, Heap.Subheap h' p.2 ∧ (p.1, h') ∈ G ∧ h' ≠ p.2 := by
  constructor
  · rintro ⟨h₀, h₁, hu, hh₀, hh₁⟩
    refine ⟨h₁, union_sub_right hu, hh₁, ?_⟩
    intro h_eq
    apply hh₀
    intro l
    rcases hu.1 l with h0 | h1
    · exact h0
    · have hcell := hu.2 l
      rw [h_eq] at h1
      rw [h1] at hcell
      cases heq : h₀.cell l with
      | none => rfl
      | some v =>
        rw [heq] at hcell
        cases hcell
  · rintro ⟨h₁, hsub, hh₁, hne⟩
    obtain ⟨h₀, hu⟩ := sub_split hsub
    refine ⟨h₀, h₁, hu, ?_, hh₁⟩
    intro hh₀
    apply hne
    apply heap_ext
    funext l
    have h0 : h₀.cell l = none := hh₀ l
    have hcell := hu.2 l
    rw [h0] at hcell
    simpa using hcell.symm

private theorem mem_subP_iff (F G : Pred) (p : State) :
    p ∈ subP F G ↔
      p ∈ F ∧ ∀ h' : Heap, Heap.Subheap h' p.2 → (p.1, h') ∈ G → h' = p.2 := by
  simp only [subP, Set.mem_inter_iff, Set.mem_compl_iff, mem_sepConj_emp_compl_iff]
  push_neg
  rfl

private theorem foldl_subP_mem (Gs : List Pred) (A : Pred) (p : State) :
    p ∈ Gs.foldl subP A ↔
      p ∈ A ∧ ∀ G ∈ Gs, ∀ h' : Heap, Heap.Subheap h' p.2 → (p.1, h') ∈ G → h' = p.2 := by
  induction Gs generalizing A with
  | nil =>
    simp
  | cons G rest ih =>
    simp only [List.foldl_cons, ih, mem_subP_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨hpA, hG⟩, hrest⟩
      refine ⟨hpA, ?_⟩
      intro G' hmem h' hsub hh'
      rcases hmem with rfl | hmem
      · exact hG h' hsub hh'
      · exact hrest G' hmem h' hsub hh'
    · rintro ⟨hpA, hall⟩
      refine ⟨⟨hpA, fun h' hsub hh' => hall G (Or.inl rfl) h' hsub hh'⟩, ?_⟩
      intro G' hmem h' hsub hh'
      exact hall G' (Or.inr hmem) h' hsub hh'

end SolBiAbductionLemma323

open SolBiAbductionLemma323

theorem solution :
    (∀ F : Pred, minSet F = subP F F) ∧
    (∀ F G H : Pred, subP (F ∪ G) H = subP F H ∪ subP G H) ∧
    (∀ (X : ℕ) (F G : Pred), NotFree X G → subP (exQ X F) G = exQ X (subP F G)) ∧
    (∀ F G H : Pred, subP F (G ∪ H) = subP F G ∩ subP F H) ∧
    (∀ (X : ℕ) (F G : Pred), NotFree X F → subP F (exQ X G) = allQ X (subP F G)) ∧
    (∀ Fs : List Pred,
      minSet (⋃ i : Fin Fs.length, Fs.get i) =
        ⋃ i : Fin Fs.length, Fs.foldl subP (Fs.get i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    ext p
    rw [mem_subP_iff]
    rfl
  · intro F G H
    exact Set.union_inter_distrib_right F G (sepConj empᶜ H)ᶜ
  · intro X F G hG
    ext ⟨s, h⟩
    simp only [mem_subP_iff, exQ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨v, hv⟩, hall⟩
      refine ⟨v, hv, ?_⟩
      intro h' hsub hh'
      exact hall h' hsub ((hG s h' v).mpr hh')
    · rintro ⟨v, hv, hall⟩
      refine ⟨⟨v, hv⟩, ?_⟩
      intro h' hsub hh'
      exact hall h' hsub ((hG s h' v).mp hh')
  · intro F G H
    ext p
    simp only [mem_subP_iff, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ⟨hpF, hall⟩
      exact ⟨⟨hpF, fun h' hsub hh' => hall h' hsub (Or.inl hh')⟩,
             ⟨hpF, fun h' hsub hh' => hall h' hsub (Or.inr hh')⟩⟩
    · rintro ⟨⟨hpF, hallG⟩, ⟨_, hallH⟩⟩
      refine ⟨hpF, ?_⟩
      intro h' hsub hh'
      rcases hh' with hh' | hh'
      · exact hallG h' hsub hh'
      · exact hallH h' hsub hh'
  · intro X F G hF
    ext ⟨s, h⟩
    simp only [mem_subP_iff, exQ, allQ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hpF, hall⟩ v
      refine ⟨(hF s h v).mp hpF, ?_⟩
      intro h' hsub hh'
      exact hall h' hsub ⟨v, hh'⟩
    · intro hall
      have h0 := hall (s X)
      rw [Function.update_eq_self] at h0
      refine ⟨h0.1, ?_⟩
      rintro h' hsub ⟨v, hh'⟩
      exact (hall v).2 h' hsub hh'
  · intro Fs
    ext p
    simp only [minSet, Set.mem_setOf_eq, Set.mem_iUnion, foldl_subP_mem]
    constructor
    · rintro ⟨⟨i, hi⟩, hall⟩
      refine ⟨i, hi, ?_⟩
      intro G hG h' hsub hh'
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hG
      exact hall h' hsub ⟨j, hh'⟩
    · rintro ⟨i, hi, hall⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      rintro h' hsub ⟨j, hj⟩
      exact hall (Fs.get j) (List.get_mem Fs j) h' hsub hj
