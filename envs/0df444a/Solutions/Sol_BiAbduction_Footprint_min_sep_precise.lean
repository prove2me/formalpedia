-- Prove2me | solution 1 for BiAbduction.Footprint.min_sep_precise
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T05:08:37.395099+00:00
-- url     : https://prove2.me/submissions/c733cef6-47fe-460d-bea4-600191be8b30

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics
import Definitions.Def_BiAbduction_Footprint_Footprint

open BiAbduction.Footprint

namespace SolBiAbductionFootprintMinSepPrecise

private theorem heap_ext {h k : Heap} (hc : h.cell = k.cell) : h = k := by
  cases h
  cases k
  cases hc
  rfl

private theorem subheap_refl (h : Heap) : Heap.Subheap h h :=
  fun _ _ hv => hv

private theorem subheap_trans {a b c : Heap}
    (hab : Heap.Subheap a b) (hbc : Heap.Subheap b c) :
    Heap.Subheap a c :=
  fun l v hv => hbc l v (hab l v hv)

private theorem union_sub_left {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.Subheap a h := by
  intro l v hv
  have hcell := hu.2 l
  rw [hv] at hcell
  exact hcell

private theorem disjoint_of_subheap_right {h₀ h₁ h₁' : Heap}
    (hd : Heap.Disjoint h₀ h₁) (hsub : Heap.Subheap h₁' h₁) :
    Heap.Disjoint h₀ h₁' := by
  intro l
  rcases hd l with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ?_
    cases h1' : h₁'.cell l with
    | none => rfl
    | some v =>
      have := hsub l v h1'
      rw [h1] at this
      cases this

private def mkUnionHeap {h₀ h₁ : Heap} (hd : Heap.Disjoint h₀ h₁) : Heap where
  cell := fun l => (h₀.cell l).or (h₁.cell l)
  nil_unalloc := by simp [h₀.nil_unalloc, h₁.nil_unalloc]
  finite_dom := (h₀.finite_dom.union h₁.finite_dom).subset (by
    intro l hl
    simp only [Set.mem_setOf_eq, Set.mem_union] at hl ⊢
    by_contra hnone
    push_neg at hnone
    simp [hnone.1, hnone.2] at hl)

private theorem isUnion_mkUnionHeap {h₀ h₁ : Heap} (hd : Heap.Disjoint h₀ h₁) :
    Heap.IsUnion (mkUnionHeap hd) h₀ h₁ :=
  ⟨hd, fun _ => rfl⟩

private theorem subheap_of_isUnion_subheap_right {h h' h₀ h₁ h₁' : Heap}
    (hu : Heap.IsUnion h h₀ h₁) (hu' : Heap.IsUnion h' h₀ h₁')
    (hsub : Heap.Subheap h₁' h₁) :
    Heap.Subheap h' h := by
  intro l v hv
  rw [hu'.2 l] at hv
  rw [hu.2 l]
  cases h0 : h₀.cell l with
  | some w =>
    rw [h0] at hv
    exact hv
  | none =>
    rw [h0, Option.none_or] at hv
    exact hsub l v hv

private theorem isUnion_cancel_left {h h₀ a b : Heap}
    (hua : Heap.IsUnion h h₀ a) (hub : Heap.IsUnion h h₀ b) :
    a = b := by
  apply heap_ext
  funext l
  have hca := hua.2 l
  have hcb := hub.2 l
  have heq : (h₀.cell l).or (a.cell l) = (h₀.cell l).or (b.cell l) :=
    hca.symm.trans hcb
  cases h0 : h₀.cell l with
  | none =>
    simpa [h0] using heq
  | some v =>
    have ha_none : a.cell l = none := by
      rcases hua.1 l with h0' | ha'
      · rw [h0] at h0'; cases h0'
      · exact ha'
    have hb_none : b.cell l = none := by
      rcases hub.1 l with h0' | hb'
      · rw [h0] at h0'; cases h0'
      · exact hb'
    rw [ha_none, hb_none]

private theorem subheap_right_of_isUnion_subheap {h h' h₀ h₁ k₁ : Heap}
    (hu : Heap.IsUnion h h₀ h₁) (hu' : Heap.IsUnion h' h₀ k₁)
    (hsub : Heap.Subheap h' h) :
    Heap.Subheap k₁ h₁ := by
  intro l v hv
  have h0_none : h₀.cell l = none := by
    rcases hu'.1 l with h0 | hk1
    · exact h0
    · rw [hv] at hk1; cases hk1
  have hh'_val : h'.cell l = some v := by
    rw [hu'.2 l, h0_none, Option.none_or, hv]
  have hh_val : h.cell l = some v := hsub l v hh'_val
  rw [hu.2 l, h0_none, Option.none_or] at hh_val
  exact hh_val

private theorem isUnion_unique_left {h h' a b : Heap}
    (hu : Heap.IsUnion h a b) (hu' : Heap.IsUnion h' a b) :
    h' = h := by
  apply heap_ext
  funext l
  rw [hu'.2 l, hu.2 l]

private theorem minSet_eq_self_of_precise (P : Pred) (hP : IsPrecise P) :
    minSet P = P := by
  ext ⟨s, h⟩
  simp only [minSet, Set.mem_setOf_eq]
  constructor
  · exact fun hp => hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    intro h' hsub hp'
    exact hP s h h' h hsub (subheap_refl h) hp' hp

end SolBiAbductionFootprintMinSepPrecise

open SolBiAbductionFootprintMinSepPrecise

theorem solution (P : Pred) (hP : IsPrecise P) :
    (∀ X : Pred, minSet (sepConj P X) = sepConj (minSet P) (minSet X)) ∧
    minSet P = P := by
  have hminP : minSet P = P := minSet_eq_self_of_precise P hP
  refine ⟨?_, hminP⟩
  intro X
  rw [hminP]
  ext ⟨s, h⟩
  constructor
  · rintro ⟨⟨h₀, h₁, hu, hp₀, hx₁⟩, hmin⟩
    refine ⟨h₀, h₁, hu, hp₀, hx₁, ?_⟩
    intro h₁' hsub₁' hx₁'
    have hd' : Heap.Disjoint h₀ h₁' := disjoint_of_subheap_right hu.1 hsub₁'
    let h' : Heap := mkUnionHeap hd'
    have hu' : Heap.IsUnion h' h₀ h₁' := isUnion_mkUnionHeap hd'
    have hsub' : Heap.Subheap h' h := subheap_of_isUnion_subheap_right hu hu' hsub₁'
    have hh'_eq : h' = h := hmin h' hsub' ⟨h₀, h₁', hu', hp₀, hx₁'⟩
    rw [hh'_eq] at hu'
    exact isUnion_cancel_left hu' hu
  · rintro ⟨h₀, h₁, hu, hp₀, hx₁, hmin₁⟩
    refine ⟨⟨h₀, h₁, hu, hp₀, hx₁⟩, ?_⟩
    rintro h' hsub' ⟨k₀, k₁, hu', hpk₀, hxk₁⟩
    have hsub_k₀ : Heap.Subheap k₀ h := subheap_trans (union_sub_left hu') hsub'
    have hsub_h₀ : Heap.Subheap h₀ h := union_sub_left hu
    have hk₀_eq : k₀ = h₀ := hP s h k₀ h₀ hsub_k₀ hsub_h₀ hpk₀ hp₀
    subst hk₀_eq
    have hsub_k₁ : Heap.Subheap k₁ h₁ := subheap_right_of_isUnion_subheap hu hu' hsub'
    have hk₁_eq : k₁ = h₁ := hmin₁ k₁ hsub_k₁ hxk₁
    subst hk₁_eq
    exact isUnion_unique_left hu hu'
