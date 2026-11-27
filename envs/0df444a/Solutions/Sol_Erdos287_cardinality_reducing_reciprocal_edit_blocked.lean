-- Prove2me | solution 1 for Erdos287.cardinality_reducing_reciprocal_edit_blocked
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:02:05.239949+00:00
-- url     : https://prove2.me/submissions/a92ab3c6-4179-426e-9efc-19eebfa6d559

import Mathlib

open Finset

set_option autoImplicit false

/-- An exact edit that reduces cardinality must lose an adjacent pair. If
only one endpoint of the pair is removed, the other is an old omission
that the edit fails to insert. -/
theorem solution (D R A : Finset ℕ) (m M : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (hR : R ⊆ D) (hmR : m ∉ R) (hA : A ⊆ Finset.Icc m M) (hAD : Disjoint A D)
    (hexact : ∑ n ∈ A, (1 : ℚ) / n = ∑ n ∈ R, (1 : ℚ) / n)
    (hsize : A.card < R.card) :
    ∃ x, m ≤ x ∧ x + 1 ≤ M ∧
      ((x ∈ R ∧ x + 1 ∈ R) ∨
        (x ∈ R ∧ x + 1 ∉ D ∧ x + 1 ∉ A) ∨
        (x + 1 ∈ R ∧ x ∉ D ∧ x ∉ A)) := by
  classical
  let E := (D \ R) ∪ A
  have hDisj : Disjoint (D \ R) A := by
    exact hAD.symm.mono_left sdiff_subset
  have hESum : ∑ n ∈ E, (1 : ℚ) / n = 1 := by
    rw [show E = (D \ R) ∪ A from rfl, sum_union hDisj, hexact, sum_sdiff hR, hsum]
  have hECard : E.card < D.card := by
    rw [show E = (D \ R) ∪ A from rfl, card_union_of_disjoint hDisj]
    have hCount := card_sdiff_add_card_eq_card hR
    omega
  have hmE : m ∈ E := mem_union_left _ (mem_sdiff.mpr ⟨hm, hmR⟩)
  have hE : E ⊆ Icc m M := union_subset (sdiff_subset.trans hD) hA
  by_contra h
  apply hECard.not_ge
  refine hmin E hmE hE (fun x hx hxx => ?_) hESum
  by_contra hmiss
  have hxD : x ∈ D → x ∈ R := by
    intro hd
    by_contra hr
    exact hmiss (Or.inl (mem_union_left _ (mem_sdiff.mpr ⟨hd, hr⟩)))
  have hxxD : x + 1 ∈ D → x + 1 ∈ R := by
    intro hd
    by_contra hr
    exact hmiss (Or.inr (mem_union_left _ (mem_sdiff.mpr ⟨hd, hr⟩)))
  by_cases hd : x ∈ D
  · by_cases hds : x + 1 ∈ D
    · exact h ⟨x, hx, hxx, Or.inl ⟨hxD hd, hxxD hds⟩⟩
    · exact h ⟨x, hx, hxx, Or.inr (Or.inl ⟨hxD hd, hds,
        fun ha => hmiss (Or.inr (mem_union_right _ ha))⟩)⟩
  · exact h ⟨x, hx, hxx, Or.inr (Or.inr ⟨hxxD ((hcover x hx hxx).resolve_left hd),
      hd, fun ha => hmiss (Or.inl (mem_union_right _ ha))⟩)⟩

