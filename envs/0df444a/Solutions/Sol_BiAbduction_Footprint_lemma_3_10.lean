-- Prove2me | solution 1 for BiAbduction.Footprint.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T05:08:35.537025+00:00
-- url     : https://prove2.me/submissions/37de767d-8619-4df4-8e79-30973e509527

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

open BiAbduction.Footprint

namespace SolBiAbductionFootprintLemma310

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

private theorem subheap_antisymm {a b : Heap}
    (hab : Heap.Subheap a b) (hba : Heap.Subheap b a) :
    a = b := by
  apply heap_ext
  funext l
  cases ha : a.cell l with
  | none =>
    cases hb : b.cell l with
    | none => rfl
    | some v =>
      have := hba l v hb
      rw [ha] at this
      cases this
  | some v =>
    exact (hab l v ha).symm

private theorem union_sub_left {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.Subheap a h := by
  intro l v hv
  have hcell := hu.2 l
  rw [hv] at hcell
  exact hcell

private theorem sub_split_left {a h : Heap} (ha : Heap.Subheap a h) :
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

private theorem mem_sepConj_univ_iff (M : Pred) (s : Stack) (h : Heap) :
    (s, h) ∈ sepConj M Set.univ ↔ ∃ h₀ : Heap, Heap.Subheap h₀ h ∧ (s, h₀) ∈ M := by
  constructor
  · rintro ⟨h₀, _, hu, hh₀, _⟩
    exact ⟨h₀, union_sub_left hu, hh₀⟩
  · rintro ⟨h₀, hsub, hh₀⟩
    obtain ⟨h₁, hu⟩ := sub_split_left hsub
    exact ⟨h₀, h₁, hu, hh₀, trivial⟩

private theorem spatialLe_iff (M M' : Pred) :
    SpatialLe M M' ↔
      ∀ (s : Stack) (h : Heap), (s, h) ∈ M' →
        ∃ h₀ : Heap, Heap.Subheap h₀ h ∧ (s, h₀) ∈ M := by
  constructor
  · intro hle s h hm'
    exact (mem_sepConj_univ_iff M s h).mp (hle hm')
  · rintro hall ⟨s, h⟩ hm'
    exact (mem_sepConj_univ_iff M s h).mpr (hall s h hm')

private noncomputable def domCard (h : Heap) : ℕ :=
  h.finite_dom.toFinset.card

private theorem dom_subset_of_subheap {a b : Heap} (hab : Heap.Subheap a b) :
    a.finite_dom.toFinset ⊆ b.finite_dom.toFinset := by
  intro l hl
  rw [Set.Finite.mem_toFinset] at hl ⊢
  cases ha : a.cell l with
  | none => exact False.elim (hl ha)
  | some v =>
    have hb := hab l v ha
    simp [hb]

private theorem domCard_lt_of_subheap_ne {a b : Heap}
    (hab : Heap.Subheap a b) (hne : a ≠ b) :
    domCard a < domCard b := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨dom_subset_of_subheap hab, ?_⟩
  intro heq
  apply hne
  apply subheap_antisymm hab
  intro l v hv
  have hmem_b : l ∈ b.finite_dom.toFinset := by
    rw [Set.Finite.mem_toFinset]
    simp [hv]
  have hmem_a : l ∈ a.finite_dom.toFinset := heq ▸ hmem_b
  rw [Set.Finite.mem_toFinset] at hmem_a
  cases ha : a.cell l with
  | none => exact False.elim (hmem_a ha)
  | some w =>
    have hbw := hab l w ha
    rw [hv] at hbw
    exact hbw.symm

private theorem exists_subheap_mem_minSet_aux (n : ℕ) (M : Pred) (s : Stack) :
    ∀ h : Heap, domCard h = n → (s, h) ∈ M →
      ∃ h₀ : Heap, Heap.Subheap h₀ h ∧ (s, h₀) ∈ minSet M := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h hcard hm
    by_cases hmin : (s, h) ∈ minSet M
    · exact ⟨h, subheap_refl h, hmin⟩
    · simp only [minSet, Set.mem_setOf_eq, hm, true_and, not_forall] at hmin
      obtain ⟨h', hsub, hm', hne⟩ := hmin
      have hlt : domCard h' < n := by
        rw [← hcard]
        exact domCard_lt_of_subheap_ne hsub hne
      obtain ⟨h₀, hsub₀, hmin₀⟩ := ih (domCard h') hlt h' rfl hm'
      exact ⟨h₀, subheap_trans hsub₀ hsub, hmin₀⟩

private theorem exists_subheap_mem_minSet (M : Pred) {s : Stack} {h : Heap}
    (hm : (s, h) ∈ M) :
    ∃ h₀ : Heap, Heap.Subheap h₀ h ∧ (s, h₀) ∈ minSet M :=
  exists_subheap_mem_minSet_aux (domCard h) M s h rfl hm

private theorem spatialLe_refl (M : Pred) : SpatialLe M M := by
  rw [spatialLe_iff]
  intro s h hm
  exact ⟨h, subheap_refl h, hm⟩

private theorem spatialLe_trans {M₁ M₂ M₃ : Pred}
    (h12 : SpatialLe M₁ M₂) (h23 : SpatialLe M₂ M₃) :
    SpatialLe M₁ M₃ := by
  rw [spatialLe_iff] at h12 h23 ⊢
  intro s h hm3
  obtain ⟨h₂, hsub2, hm2⟩ := h23 s h hm3
  obtain ⟨h₁, hsub1, hm1⟩ := h12 s h₂ hm2
  exact ⟨h₁, subheap_trans hsub1 hsub2, hm1⟩

private theorem spatialLe_minSet_right (M : Pred) : SpatialLe M (minSet M) := by
  rw [spatialLe_iff]
  intro s h hmin
  exact ⟨h, subheap_refl h, hmin.1⟩

private theorem spatialLe_minSet_left (M : Pred) : SpatialLe (minSet M) M := by
  rw [spatialLe_iff]
  intro s h hm
  exact exists_subheap_mem_minSet M hm

private theorem minSet_subset_of_spatialLe_both {M M' : Pred}
    (h1 : SpatialLe M M') (h2 : SpatialLe M' M) :
    minSet M ⊆ minSet M' := by
  rw [spatialLe_iff] at h1 h2
  rintro ⟨s, h⟩ ⟨hm, hmin⟩
  obtain ⟨h₁, hsub1, hm1'⟩ := h2 s h hm
  obtain ⟨h₀, hsub0, hm0⟩ := h1 s h₁ hm1'
  have h0_eq : h₀ = h := hmin h₀ (subheap_trans hsub0 hsub1) hm0
  have hsub_h_h1 : Heap.Subheap h h₁ := h0_eq ▸ hsub0
  have h1_eq : h₁ = h := subheap_antisymm hsub1 hsub_h_h1
  refine ⟨h1_eq ▸ hm1', ?_⟩
  intro h' hsub' hm'
  obtain ⟨h'', hsub'', hm''⟩ := h1 s h' hm'
  have h''_eq : h'' = h := hmin h'' (subheap_trans hsub'' hsub') hm''
  have hsub_h_h' : Heap.Subheap h h' := h''_eq ▸ hsub''
  exact subheap_antisymm hsub' hsub_h_h'

end SolBiAbductionFootprintLemma310

open SolBiAbductionFootprintLemma310

theorem solution :
    ((∀ M : Pred, SpatialLe M M) ∧
      (∀ M₁ M₂ M₃ : Pred, SpatialLe M₁ M₂ → SpatialLe M₂ M₃ → SpatialLe M₁ M₃)) ∧
    ∀ M M' : Pred,
      (SpatialLe M (minSet M) ∧ SpatialLe (minSet M) M) ∧
      ((SpatialLe M M' ∧ SpatialLe M' M) ↔ minSet M = minSet M') := by
  refine ⟨⟨spatialLe_refl, fun _ _ _ => spatialLe_trans⟩, ?_⟩
  intro M M'
  refine ⟨⟨spatialLe_minSet_right M, spatialLe_minSet_left M⟩, ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact Set.Subset.antisymm
      (minSet_subset_of_spatialLe_both h1 h2)
      (minSet_subset_of_spatialLe_both h2 h1)
  · intro heq
    constructor
    · have hA : SpatialLe M (minSet M') := heq ▸ spatialLe_minSet_right M
      exact spatialLe_trans hA (spatialLe_minSet_left M')
    · have hB : SpatialLe M' (minSet M) := heq.symm ▸ spatialLe_minSet_right M'
      exact spatialLe_trans hB (spatialLe_minSet_left M)
