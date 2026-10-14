-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityB.supermodular_pair_conjugate_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:47:44.750511+00:00
-- url     : https://prove2.me/submissions/29c06692-9dc6-4e75-af03-b4436369dec5

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupermodularPair



namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise

lemma spc_coord (p q x y : ℝ) :
    max p q * x + min p q * y =
      p * (if q ≤ p then x else y) + q * (if q ≤ p then y else x) := by
  split_ifs with h
  · rw [max_eq_left h, min_eq_right h]
  · push_neg at h
    rw [max_eq_right h.le, min_eq_left h.le]; ring

lemma spc_key (p q x y : Fin 2 → ℝ) :
    ∃ x' y' : Fin 2 → ℝ,
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) ∨
        (x' ⊔ y' = x ⊔ y ∧ x' ⊓ y' = x ⊓ y ∧ (x ≤ y ∨ y ≤ x))) ∧
      (∑ i, (p ⊔ q) i * x i) + (∑ i, (p ⊓ q) i * y i) ≤
        (∑ i, p i * x' i) + (∑ i, q i * y' i) := by
  by_cases hc : x ≤ y ∨ y ≤ x
  · refine ⟨fun i => if q i ≤ p i then x i else y i,
      fun i => if q i ≤ p i then y i else x i, Or.inr (Or.inr ⟨?_, ?_, hc⟩), ?_⟩
    · funext i
      simp only [Pi.sup_apply]
      split_ifs <;> simp [max_comm]
    · funext i
      simp only [Pi.inf_apply]
      split_ifs <;> simp [min_comm]
    · apply le_of_eq
      simp only [Fin.sum_univ_two, Pi.sup_apply, Pi.inf_apply]
      have h0 := spc_coord (p 0) (q 0) (x 0) (y 0)
      have h1 := spc_coord (p 1) (q 1) (x 1) (y 1)
      linarith
  · push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hxy : (y 0 < x 0 ∧ x 1 < y 1) ∨ (x 0 < y 0 ∧ y 1 < x 1) := by
      have e1 : y 0 < x 0 ∨ y 1 < x 1 := by
        by_contra h
        push_neg at h
        apply hc1
        intro i; fin_cases i
        · exact h.1
        · exact h.2
      have e2 : x 0 < y 0 ∨ x 1 < y 1 := by
        by_contra h
        push_neg at h
        apply hc2
        intro i; fin_cases i
        · exact h.1
        · exact h.2
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · linarith
      · exact Or.inl ⟨e1, e2⟩
      · exact Or.inr ⟨e2, e1⟩
      · linarith
    simp only [Fin.sum_univ_two, Pi.sup_apply, Pi.inf_apply]
    have key : (max (p 0) (q 0) * x 0 + max (p 1) (q 1) * x 1 +
        (min (p 0) (q 0) * y 0 + min (p 1) (q 1) * y 1) ≤
          p 0 * x 0 + p 1 * x 1 + (q 0 * y 0 + q 1 * y 1)) ∨
        (max (p 0) (q 0) * x 0 + max (p 1) (q 1) * x 1 +
        (min (p 0) (q 0) * y 0 + min (p 1) (q 1) * y 1) ≤
          p 0 * y 0 + p 1 * y 1 + (q 0 * x 0 + q 1 * x 1)) := by
      rcases le_total (p 0) (q 0) with h0 | h0
      · rw [max_eq_right h0, min_eq_left h0]
        rcases le_total (p 1) (q 1) with h1 | h1
        · rw [max_eq_right h1, min_eq_left h1]
          right; linarith
        · rw [max_eq_left h1, min_eq_right h1]
          rcases hxy with ⟨a, b⟩ | ⟨a, b⟩
          · right; nlinarith
          · left; nlinarith
      · rw [max_eq_left h0, min_eq_right h0]
        rcases le_total (p 1) (q 1) with h1 | h1
        · rw [max_eq_right h1, min_eq_left h1]
          rcases hxy with ⟨a, b⟩ | ⟨a, b⟩
          · left; nlinarith
          · right; nlinarith
        · rw [max_eq_left h1, min_eq_right h1]
          left; linarith
    rcases key with k | k
    · exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, by simpa [Fin.sum_univ_two] using k⟩
    · exact ⟨y, x, Or.inr (Or.inl ⟨rfl, rfl⟩), by simpa [Fin.sum_univ_two] using k⟩

lemma spc_elem (f : (Fin 2 → ℝ) → WithTop ℝ) (r x : Fin 2 → ℝ) (a : ℝ)
    (h : f x = (a : WithTop ℝ)) :
    (((∑ i, r i * x i) - a : ℝ) : EReal) ≤ ConvexConjugateR f r := by
  apply le_sSup
  refine ⟨x, ?_⟩
  rw [h, EReal.coe_sub]
  rfl

lemma spc_ub (f : (Fin 2 → ℝ) → WithTop ℝ) (r : Fin 2 → ℝ) (M : EReal)
    (h : ∀ x : Fin 2 → ℝ, ∀ a : ℝ, f x = (a : WithTop ℝ) →
      (((∑ i, r i * x i) - a : ℝ) : EReal) ≤ M) :
    ConvexConjugateR f r ≤ M := by
  apply sSup_le
  rintro v ⟨x, rfl⟩
  cases hfx : f x with
  | top =>
    show ((∑ i, r i * x i : ℝ) : EReal) - ⊤ ≤ M
    simp
  | coe a =>
    have := h x a hfx
    rw [EReal.coe_sub] at this
    exact this

lemma spc_real_of (e : EReal) (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : ∃ a : ℝ, e = (a : EReal) :=
  ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩

theorem spc_core (f : (Fin 2 → ℝ) → WithTop ℝ) (hf : SupermodularPair f) :
    ∀ p q : Fin 2 → ℝ, ConvexConjugateRW f p + ConvexConjugateRW f q ≥
      ConvexConjugateRW f (p ⊔ q) + ConvexConjugateRW f (p ⊓ q) := by
  intro p q
  by_cases hdom : ∀ x, f x = ⊤
  · have hb : ∀ r, ConvexConjugateR f r = ⊥ := by
      intro r
      apply le_antisymm _ bot_le
      apply spc_ub
      intro x a hx
      rw [hdom x] at hx
      exact absurd hx (by simp)
    have : ConvexConjugateRW f p = ⊤ := by
      unfold ConvexConjugateRW; rw [hb]; rfl
    rw [this, top_add]
    exact le_top
  push_neg at hdom
  obtain ⟨x0, hx0⟩ := hdom
  obtain ⟨a0, ha0⟩ := WithTop.ne_top_iff_exists.mp hx0
  have hnb : ∀ r, ConvexConjugateR f r ≠ ⊥ := by
    intro r h
    have := spc_elem f r x0 a0 ha0.symm
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  by_cases hA : ConvexConjugateR f p = ⊤
  · have : ConvexConjugateRW f p = ⊤ := by
      unfold ConvexConjugateRW; rw [hA]; rfl
    rw [this, top_add]
    exact le_top
  by_cases hB : ConvexConjugateR f q = ⊤
  · have : ConvexConjugateRW f q = ⊤ := by
      unfold ConvexConjugateRW; rw [hB]; rfl
    rw [this, add_top]
    exact le_top
  obtain ⟨A, hA'⟩ := spc_real_of _ hA (hnb p)
  obtain ⟨B, hB'⟩ := spc_real_of _ hB (hnb q)
  -- the key real inequality
  have H : ∀ x y : Fin 2 → ℝ, ∀ a b : ℝ, f x = (a : WithTop ℝ) → f y = (b : WithTop ℝ) →
      ((∑ i, (p ⊔ q) i * x i) - a) + ((∑ i, (p ⊓ q) i * y i) - b) ≤ A + B := by
    intro x y a b hx hy
    obtain ⟨x', y', hcase, hT⟩ := spc_key p q x y
    have hle : f x' + f y' ≤ f x + f y := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hs, hi, hc⟩
      · exact le_rfl
      · rw [add_comm]
      · have := hf x' y'
        rw [hs, hi] at this
        rcases hc with hc | hc
        · rw [sup_eq_right.mpr hc, inf_eq_left.mpr hc] at this
          exact this.trans (le_of_eq (add_comm _ _))
        · rw [sup_eq_left.mpr hc, inf_eq_right.mpr hc] at this
          exact this
    rw [hx, hy, ← WithTop.coe_add] at hle
    have hx'top : f x' ≠ ⊤ := by
      intro h; rw [h, top_add] at hle; exact WithTop.coe_ne_top (top_le_iff.mp hle)
    have hy'top : f y' ≠ ⊤ := by
      intro h; rw [h, add_top] at hle; exact WithTop.coe_ne_top (top_le_iff.mp hle)
    obtain ⟨a', ha'⟩ := WithTop.ne_top_iff_exists.mp hx'top
    obtain ⟨b', hb'⟩ := WithTop.ne_top_iff_exists.mp hy'top
    rw [← ha', ← hb', ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    have e1 := spc_elem f p x' a' ha'.symm
    have e2 := spc_elem f q y' b' hb'.symm
    rw [hA', EReal.coe_le_coe_iff] at e1
    rw [hB', EReal.coe_le_coe_iff] at e2
    linarith
  -- C is finite
  have hC : ConvexConjugateR f (p ⊔ q) ≤
      ((A + B - ((∑ i, (p ⊓ q) i * x0 i) - a0) : ℝ) : EReal) := by
    apply spc_ub
    intro x a hx
    rw [EReal.coe_le_coe_iff]
    have := H x x0 a a0 hx ha0.symm
    linarith
  have hCt : ConvexConjugateR f (p ⊔ q) ≠ ⊤ := by
    intro h; rw [h] at hC; exact EReal.coe_ne_top _ (top_le_iff.mp hC)
  obtain ⟨C, hC'⟩ := spc_real_of _ hCt (hnb _)
  have hD : ConvexConjugateR f (p ⊓ q) ≤ ((A + B - C : ℝ) : EReal) := by
    apply spc_ub
    intro y b hy
    rw [EReal.coe_le_coe_iff]
    have hC2 : ConvexConjugateR f (p ⊔ q) ≤
        ((A + B - ((∑ i, (p ⊓ q) i * y i) - b) : ℝ) : EReal) := by
      apply spc_ub
      intro x a hx
      rw [EReal.coe_le_coe_iff]
      have := H x y a b hx hy
      linarith
    rw [hC', EReal.coe_le_coe_iff] at hC2
    linarith
  have hDt : ConvexConjugateR f (p ⊓ q) ≠ ⊤ := by
    intro h; rw [h] at hD; exact EReal.coe_ne_top _ (top_le_iff.mp hD)
  obtain ⟨D, hD'⟩ := spc_real_of _ hDt (hnb _)
  rw [hD', EReal.coe_le_coe_iff] at hD
  unfold ConvexConjugateRW
  rw [hA', hB', hC', hD']
  show ((A : WithTop ℝ) + (B : WithTop ℝ)) ≥ (C : WithTop ℝ) + (D : WithTop ℝ)
  rw [← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe]
  linarith

end DiscreteConvex.ConjugacyDualityB

open DiscreteConvex.ConjugacyDualityB


theorem solution (f : (Fin 2 → ℝ) → WithTop ℝ)
    (hf : SupermodularPair f) :
    ∀ p q : Fin 2 → ℝ, ConvexConjugateRW f p + ConvexConjugateRW f q ≥
      ConvexConjugateRW f (p ⊔ q) + ConvexConjugateRW f (p ⊓ q) := by
  exact spc_core f hf
