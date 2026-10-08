-- Prove2me | solution 1 for DoubleGreedyUSM.Randomized.inequality_3
-- status  : ACCEPTED   (prove)
-- author  : @techtao
-- created : 2026-10-05T03:54:20.824985+00:00
-- url     : https://prove2.me/submissions/c47da2f3-e416-478b-a788-e09e3257930e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

/- Prove2Me target: 1fbb6a27-eac3-425b-b9bb-486fc55d65f6
Exact target: DoubleGreedyUSM.Randomized.inequality_3.
Locally prepared solution. Server acceptance has not been obtained.
Source: Buchbinder et al., FOCS 2012, inequality (3), Lemma III.1.
No target theorem or unproved platform theorem is imported. -/

private theorem nested_marginal_sum_nonneg {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B)
    (X Y : Finset α) (u : α) (hXY : X ⊆ Y) (huY : u ∈ Y) (huX : u ∉ X) :
    0 ≤ (f (insert u X) - f X) + (f (Y.erase u) - f Y) := by
  have hunion : insert u X ∪ Y.erase u = Y := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((rfl | hx) | ⟨_, hx⟩)
      · exact huY
      · exact hXY hx
      · exact hx
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl (Or.inl hxu)
      · exact Or.inr ⟨hxu, hx⟩
  have hinter : insert u X ∩ Y.erase u = X := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨h | hx, hne, _⟩
      · exact False.elim (hne h)
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_, hXY hx⟩
      intro hxu
      subst x
      exact huX hx
  have h := hf (insert u X) (Y.erase u)
  rw [hunion, hinter] at h
  linarith

private theorem comparison_losses_when_mem {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B)
    (X O : Finset α) (u : α) (hXO : X ⊆ O) (huO : u ∈ O) (huX : u ∉ X) :
    (f O - f (insert u O) = 0) ∧
      (f O - f (O.erase u) ≤ f (insert u X) - f X) := by
  constructor
  · simp [Finset.insert_eq_of_mem huO]
  · have h := nested_marginal_sum_nonneg f hf X O u hXO huO huX
    linarith

private theorem comparison_losses_when_not_mem {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B)
    (O Y : Finset α) (u : α) (hOY : O ⊆ Y) (huY : u ∈ Y) (huO : u ∉ O) :
    (f O - f (O.erase u) = 0) ∧
      (f O - f (insert u O) ≤ f (Y.erase u) - f Y) := by
  constructor
  · simp [Finset.erase_eq_of_notMem huO]
  · have h := nested_marginal_sum_nonneg f hf O Y u hOY huY huO
    linarith


/-- Exact quantified type of the platform target (namespace removed and
declaration renamed to `solution` as required by the submission interface). -/
theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (Xs Ys O : Finset X) (u : X) (hsub : Xs ⊆ Ys)
    (huY : u ∈ Ys) (huX : u ∉ Xs)
    (ha : 0 ≤ f (insert u Xs) - f Xs)
    (hb : 0 < f (Ys.erase u) - f Ys) :
    let a := f (insert u Xs) - f Xs
    let b := f (Ys.erase u) - f Ys
    let P := (O ∪ Xs) ∩ Ys
    a / (a + b) * (f P - f (insert u P)) +
      b / (a + b) * (f P - f (P.erase u)) ≤ a * b / (a + b) := by
  let a := f (insert u Xs) - f Xs
  let b := f (Ys.erase u) - f Ys
  let P := (O ∪ Xs) ∩ Ys
  change a / (a + b) * (f P - f (insert u P)) +
      b / (a + b) * (f P - f (P.erase u)) ≤ a * b / (a + b)
  have ha' : 0 ≤ a := ha
  have hb' : 0 < b := hb
  have hden : 0 < a + b := by linarith
  have hXp : Xs ⊆ P := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr hx), hsub hx⟩
  have hpY : P ⊆ Ys := Finset.inter_subset_right
  have hfa : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B := hf
  by_cases huP : u ∈ P
  · have h := comparison_losses_when_mem f hfa Xs P u hXp huP huX
    rw [h.1, mul_zero, zero_add]
    calc
      b / (a + b) * (f P - f (P.erase u)) ≤ b / (a + b) * a :=
        mul_le_mul_of_nonneg_left h.2 (div_nonneg hb'.le hden.le)
      _ = a * b / (a + b) := by ring
  · have h := comparison_losses_when_not_mem f hfa P Ys u hpY huY huP
    rw [h.1, mul_zero, add_zero]
    calc
      a / (a + b) * (f P - f (insert u P)) ≤ a / (a + b) * b :=
        mul_le_mul_of_nonneg_left h.2 (div_nonneg ha' hden.le)
      _ = a * b / (a + b) := by ring

#print axioms solution

