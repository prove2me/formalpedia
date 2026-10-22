-- Prove2me | solution 1 for CompOT.Vertices.prop_3_4_cycle_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:02:18.466632+00:00
-- url     : https://prove2.me/submissions/22e44a7f-b5d3-475c-a2cf-c255e5f11bd8

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

set_option autoImplicit false
open CompOT.Vertices

namespace CycAux

variable {n m : ℕ}

/-- elementary matrix of an undirected pair of nodes -/
noncomputable def Mx (u y : Fin n ⊕ Fin m) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => if s(u, y) = s(Sum.inl i, Sum.inr j) then 1 else 0

/-- alternating sum of elementary matrices along a walk -/
noncomputable def Fw (P : Matrix (Fin n) (Fin m) ℝ) :
    {u v : Fin n ⊕ Fin m} → (supportGraph P).Walk u v → Matrix (Fin n) (Fin m) ℝ
  | _, _, SimpleGraph.Walk.nil => 0
  | u, _, SimpleGraph.Walk.cons (v := x) _ w => Mx u x - Fw P w

/-- row/column sum at a node -/
def Sx (x : Fin n ⊕ Fin m) (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  Sum.elim (fun i => ∑ j, A i j) (fun j => ∑ i, A i j) x

lemma Sx_sub (x : Fin n ⊕ Fin m) (A B : Matrix (Fin n) (Fin m) ℝ) :
    Sx x (A - B) = Sx x A - Sx x B := by
  cases x <;> simp [Sx, Finset.sum_sub_distrib]

lemma Sx_zero (x : Fin n ⊕ Fin m) : Sx x (0 : Matrix (Fin n) (Fin m) ℝ) = 0 := by
  cases x <;> simp [Sx]

lemma Mx_lr (i0 : Fin n) (j1 : Fin m) (i : Fin n) (j : Fin m) :
    Mx (Sum.inl i0) (Sum.inr j1) i j = if i = i0 ∧ j = j1 then 1 else 0 := by
  simp only [Mx, Matrix.of_apply, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    or_false]
  by_cases h1 : i0 = i <;> by_cases h2 : j1 = j <;> simp [h1, h2, eq_comm]

lemma Mx_rl (j0 : Fin m) (i1 : Fin n) (i : Fin n) (j : Fin m) :
    Mx (Sum.inr j0) (Sum.inl i1) i j = if i = i1 ∧ j = j0 then 1 else 0 := by
  simp only [Mx, Matrix.of_apply, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_or]
  by_cases h1 : i1 = i <;> by_cases h2 : j0 = j <;> simp [h1, h2, eq_comm]

lemma Sx_lr (i0 : Fin n) (j1 : Fin m) (x : Fin n ⊕ Fin m) :
    Sx x (Mx (Sum.inl i0) (Sum.inr j1)) =
      (if x = Sum.inl i0 then 1 else 0) + (if x = Sum.inr j1 then 1 else 0) := by
  cases x with
  | inl i =>
    simp only [Sx, Sum.elim_inl, Mx_lr]
    by_cases h : i = i0 <;> simp [h]
  | inr j =>
    simp only [Sx, Sum.elim_inr, Mx_lr]
    by_cases h : j = j1 <;> simp [h]

lemma Sx_Mx (P : Matrix (Fin n) (Fin m) ℝ) (x u y : Fin n ⊕ Fin m)
    (h : (supportGraph P).Adj u y) :
    Sx x (Mx u y) = (if x = u then 1 else 0) + (if x = y then 1 else 0) := by
  rcases u with i0 | j0 <;> rcases y with i1 | j1
  · exact absurd h (by simp [supportGraph, supportRel])
  · exact Sx_lr i0 j1 x
  · have : Mx (Sum.inr j0) (Sum.inl i1) = Mx (Sum.inl i1) (Sum.inr j0) := by
      funext i j; simp only [Mx, Matrix.of_apply, Sym2.eq_swap]
    rw [this, Sx_lr]; ring
  · exact absurd h (by simp [supportGraph, supportRel])

lemma Sx_Fw (P : Matrix (Fin n) (Fin m) ℝ) (x : Fin n ⊕ Fin m) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) :
    Sx x (Fw P w) = (if x = u then 1 else 0) - (-1 : ℝ) ^ w.length * (if x = v then 1 else 0) := by
  induction w with
  | nil => simp [Fw, Sx_zero]
  | @cons u y v h w ih =>
    rw [Fw, Sx_sub, Sx_Mx P x u y h, ih, SimpleGraph.Walk.length_cons, pow_succ]
    ring

lemma isLeft_flip (P : Matrix (Fin n) (Fin m) ℝ) {u y : Fin n ⊕ Fin m}
    (h : (supportGraph P).Adj u y) : u.isLeft = !y.isLeft := by
  rcases u with i0 | j0 <;> rcases y with i1 | j1
  · exact absurd h (by simp [supportGraph, supportRel])
  · rfl
  · rfl
  · exact absurd h (by simp [supportGraph, supportRel])

lemma even_closed (P : Matrix (Fin n) (Fin m) ℝ) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) : (Even w.length ↔ u.isLeft = v.isLeft) := by
  induction w with
  | nil => simp
  | @cons u y v h w ih =>
    have := isLeft_flip P h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih, this]
    cases hy : y.isLeft <;> cases hv : v.isLeft <;> simp

lemma Fw_support (P : Matrix (Fin n) (Fin m) ℝ) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) (i : Fin n) (j : Fin m) (h : Fw P w i j ≠ 0) :
    s(Sum.inl i, Sum.inr j) ∈ w.edges := by
  induction w with
  | nil => simp [Fw] at h
  | @cons u y v hh w ih =>
    rw [Fw] at h
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
    by_cases h1 : Fw P w i j = 0
    · left
      rw [Matrix.sub_apply, h1, sub_zero] at h
      simp only [Mx, Matrix.of_apply] at h
      by_contra hne
      exact h (by simp [Ne.symm hne])
    · right; exact ih h1

lemma Fw_ne_zero (P : Matrix (Fin n) (Fin m) ℝ) {v : Fin n ⊕ Fin m}
    (c : (supportGraph P).Walk v v) (hc : c.IsCycle) : Fw P c ≠ 0 := by
  cases c with
  | nil => exact absurd hc (by simp)
  | @cons _ y _ h p =>
    rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
    obtain ⟨_, hnot⟩ := hc
    intro hz
    rcases v with i | j <;> rcases y with i' | j'
    · exact absurd h (by simp [supportGraph, supportRel])
    · have h0 := congrFun (congrFun hz i) j'
      have hz2 : Fw P p i j' = 0 := by
        by_contra hne
        exact hnot (Fw_support P p i j' hne)
      rw [Fw, Matrix.sub_apply, Mx_lr, hz2] at h0
      simp at h0
    · have h0 := congrFun (congrFun hz i') j
      have hz2 : Fw P p i' j = 0 := by
        by_contra hne
        apply hnot
        rw [Sym2.eq_swap]
        exact Fw_support P p i' j hne
      rw [Fw, Matrix.sub_apply, Mx_rl, hz2] at h0
      simp at h0
    · exact absurd h (by simp [supportGraph, supportRel])

end CycAux

open CycAux in
theorem solution {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hcyc : ¬ (supportGraph P).IsAcyclic) :
    ∃ E : Matrix (Fin n) (Fin m) ℝ, E ≠ 0 ∧
      (∀ i, ∑ j, E i j = 0) ∧ (∀ j, ∑ i, E i j = 0) ∧
      (∀ i j, E i j ≠ 0 → 0 < P i j) := by
  unfold SimpleGraph.IsAcyclic at hcyc
  push Not at hcyc
  obtain ⟨v, c, hc⟩ := hcyc
  have hev : Even c.length := (even_closed P c).2 rfl
  refine ⟨Fw P c, Fw_ne_zero P c hc, ?_, ?_, ?_⟩
  · intro i
    have := Sx_Fw P (Sum.inl i) c
    simp only [Sx, Sum.elim_inl, hev.neg_one_pow] at this
    rw [this]; ring
  · intro j
    have := Sx_Fw P (Sum.inr j) c
    simp only [Sx, Sum.elim_inr, hev.neg_one_pow] at this
    rw [this]; ring
  · intro i j h
    have h1 := Fw_support P c i j h
    have h2 := c.edges_subset_edgeSet h1
    rw [SimpleGraph.mem_edgeSet] at h2
    exact h2
