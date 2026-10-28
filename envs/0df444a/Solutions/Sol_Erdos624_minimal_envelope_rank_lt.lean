-- Prove2me | solution 1 for Erdos624.minimal_envelope_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:42:39.651024+00:00
-- url     : https://prove2.me/submissions/490d993f-3885-4861-8bcc-387727403bfb

import Mathlib
open Finset

namespace E624R12B
open Finset Module

variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]

/-- generators of the minimal-witness envelope -/
def gen (L : Finset U → Finset C) (k : ℕ) (u : C) : Set (U → ZMod 2) :=
  {v | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧ (∀ A' ⊂ A, u ∉ L A') ∧
    v = fun x => if x ∈ A then 1 else 0}

lemma chi_eq_sum (H : Finset U) :
    (fun x => if x ∈ H then (1 : ZMod 2) else 0) = ∑ x ∈ H, Pi.single x (1 : ZMod 2) := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]

lemma span_single_top : Submodule.span (ZMod 2) (Set.range fun x : U => Pi.single x (1 : ZMod 2)) = ⊤ := by
  have h := (Pi.basisFun (ZMod 2) U).span_eq
  rw [show ⇑(Pi.basisFun (ZMod 2) U) = fun x => Pi.single x 1 from
    funext fun x => Pi.basisFun_apply _ _ _] at h
  exact h

/-- minimal witness inside a non-hole -/
lemma exists_min_witness (L : Finset U → Finset C) (u : C) (A : Finset U) (hA : u ∈ L A) :
    ∃ H ⊆ A, u ∈ L H ∧ ∀ H' ⊂ H, u ∉ L H' := by
  have hne : (A.powerset.filter (fun B => u ∈ L B)).Nonempty :=
    ⟨A, mem_filter.2 ⟨mem_powerset_self _, hA⟩⟩
  obtain ⟨H, hH, hmin⟩ := exists_min_image _ card hne
  rw [mem_filter, mem_powerset] at hH
  refine ⟨H, hH.1, hH.2, fun H' hH' huH' => ?_⟩
  have := hmin H' (mem_filter.2 ⟨mem_powerset.2 (hH'.1.trans hH.1), huH'⟩)
  have := card_lt_card hH'
  omega

/-- The zero-sum property of a minimal witness of size ≤ k. -/
lemma witness_sum_zero (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (H : Finset U) (hHk : #H ≤ k) (huH : u ∈ L H) (hmin : ∀ H' ⊂ H, u ∉ L H') :
    ∑ x ∈ H, (Submodule.span (ZMod 2) (gen L k u)).mkQ (Pi.single x 1) = 0 := by
  rw [← map_sum, ← chi_eq_sum, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  refine ⟨H, ?_, hHk, huH, hmin, rfl⟩
  rw [card_pos]; by_contra h; rw [not_nonempty_iff_eq_empty] at h; subst h; exact hu huH

theorem extension (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (B : Finset U) (hB : #B ≤ k) (hBhole : ∀ A ⊆ B, u ∉ L A) :
    ∃ B' : Finset U, B ⊆ B' ∧ (∀ A ⊆ B', u ∉ L A) ∧
      #B' = min k (finrank (ZMod 2) ((U → ZMod 2) ⧸ Submodule.span (ZMod 2) (gen L k u)) +
        (#B - finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((fun x => (Submodule.span (ZMod 2) (gen L k u)).mkQ (Pi.single x 1)) '' (B : Set U))))) := by
  classical
  set Z := Submodule.span (ZMod 2) (gen L k u) with hZ
  set Q := (U → ZMod 2) ⧸ Z
  set q : U → Q := fun x => Z.mkQ (Pi.single x 1) with hq
  set SB : Submodule (ZMod 2) Q := Submodule.span (ZMod 2) (q '' (B : Set U)) with hSB
  set r := finrank (ZMod 2) Q with hr
  set ρ := finrank (ZMod 2) SB with hρ
  set π := SB.mkQ with hπ
  set v : U → Q ⧸ SB := fun x => π (q x) with hv
  have hρr : ρ ≤ r := Submodule.finrank_le SB
  have hρB : ρ ≤ #B := by
    have := finrank_span_finset_le_card (R := ZMod 2) (B.image q)
    rw [coe_image, Set.finrank, ← hSB] at this
    exact this.trans card_image_le
  have hquot : finrank (ZMod 2) (Q ⧸ SB) + ρ = r := Submodule.finrank_quotient_add_finrank SB
  -- v spans
  have hspan : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
    have hsurj : Function.Surjective (π.comp Z.mkQ) :=
      (Submodule.mkQ_surjective SB).comp (Submodule.mkQ_surjective Z)
    have : Set.range v = (π.comp Z.mkQ) '' Set.range (fun x : U => Pi.single x (1 : ZMod 2)) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, span_single_top, Submodule.map_top,
      LinearMap.range_eq_top.2 hsurj]
  obtain ⟨b, -, -, hbspan, hbind⟩ := exists_linearIndepOn_extension (K := ZMod 2) (v := v)
    (s := ∅) (t := Set.univ) (linearIndepOn_empty _ _) (Set.empty_subset _)
  have hbtop : Submodule.span (ZMod 2) (v '' b) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hbspan ⟨x, Set.mem_univ _, rfl⟩
  set X := b.toFinset with hX
  have hXind : LinearIndepOn (ZMod 2) v (X : Set U) := by rw [hX, Set.coe_toFinset]; exact hbind
  have hXcard : #X = r - ρ := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hbind
    have h2 : Set.range (fun x : b => v x) = v '' b := by ext; simp
    rw [h2, Set.finrank, hbtop, finrank_top] at h1
    rw [hX, Set.toFinset_card]
    omega
  have hXB : Disjoint X B := by
    rw [disjoint_left]; intro x hxX hxB
    have h0 : v x = 0 := by
      simp only [hv, hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, hxB, rfl⟩
    exact hXind.ne_zero (by simpa using hxX) h0
  set t := min (k - #B) (r - ρ) with ht
  obtain ⟨X', hX'X, hX'card⟩ := exists_subset_card_eq (show t ≤ #X by rw [hXcard]; omega)
  have hX'ind : LinearIndepOn (ZMod 2) v (X' : Set U) := hXind.mono (by exact_mod_cast hX'X)
  refine ⟨B ∪ X', subset_union_left, ?_, ?_⟩
  · intro A hA huA
    obtain ⟨H, hHA, huH, hmin⟩ := exists_min_witness L u A huA
    have hHB' : H ⊆ B ∪ X' := hHA.trans hA
    have hcardB' : #(B ∪ X') ≤ k := by
      rw [card_union_of_disjoint (disjoint_of_subset_right hX'X hXB.symm)]; omega
    have hsum := witness_sum_zero L k u hu H ((card_le_card hHB').trans hcardB') huH hmin
    have hsumv : ∑ x ∈ H, v x = 0 := by
      simp only [hv, ← map_sum]
      rw [← hZ] at hsum
      change π (∑ x ∈ H, q x) = 0
      rw [show (∑ x ∈ H, q x) = 0 from hsum, map_zero]
    have hBzero : ∀ x ∈ B, v x = 0 := by
      intro x hxB
      simp only [hv, hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, hxB, rfl⟩
    have hsplit : ∑ x ∈ H, v x = ∑ x ∈ H \ B, v x := by
      rw [← sum_sdiff (inter_subset_left : H ∩ B ⊆ H)]
      rw [sum_eq_zero (fun x hx => hBzero x (mem_inter.1 hx).2), add_zero]
      congr 1; ext x; simp
    rw [hsplit] at hsumv
    have hsub : ((H \ B : Finset U) : Set U) ⊆ X' := by
      intro x hx
      rw [coe_sdiff, Set.mem_sdiff] at hx
      have := hHB' (by exact_mod_cast hx.1)
      rcases mem_union.1 this with h | h
      · exact absurd (by exact_mod_cast h) hx.2
      · exact_mod_cast h
    have hall := (linearIndepOn_iff'.1 hX'ind) (H \ B) (fun _ => 1) hsub
      (by simpa using hsumv)
    have hempty : H \ B = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
      exact one_ne_zero (hall x hx)
    have hHB : H ⊆ B := by
      intro x hx; by_contra hxB
      have : x ∈ H \ B := mem_sdiff.2 ⟨hx, hxB⟩
      rw [hempty] at this; simp at this
    exact hBhole H hHB huH
  · rw [card_union_of_disjoint (disjoint_of_subset_right hX'X hXB.symm), hX'card, ht]
    omega

theorem rank_lt (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A) :
    finrank (ZMod 2) ((U → ZMod 2) ⧸ Submodule.span (ZMod 2) (gen L k u)) < k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B', -, hhole, hcard⟩ := extension L k u hu ∅ (by simp) (by
    intro A hA; rw [subset_empty] at hA; subst hA; exact hu)
  simp at hcard
  rw [min_eq_left hcon] at hcard
  obtain ⟨A, hA, huA⟩ := hcov B' hcard
  exact hhole A hA huA

end E624R12B

namespace Erdos624

theorem minimal_envelope_rank_lt {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A) :
    (Module.finrank (ZMod 2) ((U → ZMod 2) ⧸
      Submodule.span (ZMod 2) {v : U → ZMod 2 | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧
        (∀ A' ⊂ A, u ∉ L A') ∧ v = fun x => if x ∈ A then 1 else 0})) < k := by
  exact E624R12B.rank_lt L k u hu hcov

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A) :
    (Module.finrank (ZMod 2) ((U → ZMod 2) ⧸
      Submodule.span (ZMod 2) {v : U → ZMod 2 | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧
        (∀ A' ⊂ A, u ∉ L A') ∧ v = fun x => if x ∈ A then 1 else 0})) < k :=
  Erdos624.minimal_envelope_rank_lt L k u hu hcov
