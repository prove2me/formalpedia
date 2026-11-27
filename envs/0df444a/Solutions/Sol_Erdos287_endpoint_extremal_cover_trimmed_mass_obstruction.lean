-- Prove2me | solution 1 for Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:22:18.400804+00:00
-- url     : https://prove2.me/submissions/471f67f2-18c1-4f4c-993d-da1a0ce44324

import Mathlib

open Finset

set_option autoImplicit false

/-- Trimming either endpoint of an endpoint-extremal exact pair cover
leaves a reciprocal deficit that cannot be filled by old omissions inside
the retained interval. -/
theorem solution (D A : Finset ℕ) (m M l u : ℕ) (hm : 1 < m)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hextreme : ∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m))
    (hml : m ≤ l) (huM : u ≤ M) (htrim : m < l ∨ u < M)
    (hA : A ⊆ Finset.Icc l u) (hAD : Disjoint A D) :
    (∑ n ∈ A, (1 : ℚ) / n) ≠
      ∑ n ∈ D.filter (fun n => n < l ∨ u < n), (1 : ℚ) / n := by
  classical
  intro hsame
  let R := D.filter (fun n => n < l ∨ u < n)
  let E := (D \ R) ∪ A
  have hR : R ⊆ D := filter_subset _ _
  have hdisj : Disjoint (D \ R) A := hAD.symm.mono_left sdiff_subset
  have hsumE : ∑ n ∈ E, (1 : ℚ) / n = 1 := by
    change (∑ n ∈ (D \ R) ∪ A, (1 : ℚ) / n) = 1
    change (∑ n ∈ A, (1 : ℚ) / n) = ∑ n ∈ R, (1 : ℚ) / n at hsame
    rw [sum_union hdisj, hsame, sum_sdiff hR, hsum]
  have hE : E ⊆ Icc l u := by
    apply union_subset _ hA
    intro x hx
    have hdx := mem_sdiff.mp hx
    apply mem_Icc.mpr
    constructor
    · exact le_of_not_gt fun h => hdx.2 (mem_filter.mpr ⟨hdx.1, Or.inl h⟩)
    · exact le_of_not_gt fun h => hdx.2 (mem_filter.mpr ⟨hdx.1, Or.inr h⟩)
  have hnonempty : E.Nonempty := by
    by_contra! h
    rw [h, sum_empty] at hsumE
    norm_num at hsumE
  let a := E.min' hnonempty
  let b := E.max' hnonempty
  have ha : a ∈ E := E.min'_mem hnonempty
  have hb : b ∈ E := E.max'_mem hnonempty
  have hla : l ≤ a := (mem_Icc.mp (hE ha)).1
  have hbu : b ≤ u := (mem_Icc.mp (hE hb)).2
  have hBounds : E ⊆ Icc a b := fun x hx => mem_Icc.mpr ⟨E.min'_le x hx, E.le_max' x hx⟩
  have keep (x : ℕ) (hx : x ∈ D) (h₁ : l ≤ x) (h₂ : x ≤ u) : x ∈ E :=
    mem_union_left _ (mem_sdiff.mpr ⟨hx,
      fun hr => (mem_filter.mp hr).2.elim h₁.not_gt h₂.not_gt⟩)
  have hcover' (x : ℕ) (hx : a ≤ x) (hxx : x + 1 ≤ b) : x ∈ E ∨ x + 1 ∈ E := by
    have hlx := hla.trans hx
    have hxu := hxx.trans hbu
    rcases hcover x (hml.trans hlx) (hxu.trans huM) with h | h
    · exact Or.inl (keep x h hlx (by omega))
    · exact Or.inr (keep (x + 1) h (by omega) hxu)
  obtain ⟨hMb, hlower⟩ := hextreme a b E (by omega) ha hb hBounds hcover' hsumE
  have hbM : b = M := by omega
  have hma := hlower hbM
  omega

