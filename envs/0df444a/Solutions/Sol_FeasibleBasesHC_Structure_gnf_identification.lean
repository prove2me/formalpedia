-- Prove2me | solution 1 for FeasibleBasesHC.Structure.gnf_identification
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T17:14:43.872999+00:00
-- url     : https://prove2.me/submissions/dea0399c-942d-4794-8f95-4c5189bc93eb

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

open FeasibleBasesHC.Structure

namespace HCGnfAux

variable {n : ℕ} [NeZero n]

lemma sum_arcs (G : Digraph n) (beta : ℝ) (g : GpArc n → ℝ) :
    ∑ a ∈ (Gp G beta).arcs, g a =
      ∑ e ∈ G.E, g (Sum.inl e) + ∑ j ∈ Finset.univ.erase (0 : Fin n), g (Sum.inr j) := by
  have hdisj : Disjoint (G.E.image (Sum.inl : _ → GpArc n))
      ((Finset.univ.erase (0 : Fin n)).image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    cases hj
  show ∑ a ∈ G.E.image Sum.inl ∪ (Finset.univ.erase (0 : Fin n)).image Sum.inr, g a = _
  rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => Sum.inl_injective h),
    Finset.sum_image (fun a _ b _ h => Sum.inr_injective h)]

lemma out_inr (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    ∑ a ∈ (Gp G beta).arcs.filter (fun a => (Gp G beta).tail a = Sum.inr i), splitFlow x y a =
      outflow G x i := by
  rw [Finset.sum_filter, sum_arcs, outflow, Finset.sum_filter]
  simp [Gp, splitFlow]

lemma in_inr (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    ∑ a ∈ (Gp G beta).arcs.filter (fun a => (Gp G beta).head a = Sum.inr i),
      (Gp G beta).mu a * splitFlow x y a = if i = 0 then 0 else y i := by
  rw [Finset.sum_filter, sum_arcs]
  simp only [Gp, splitFlow, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add,
    Sum.inr.injEq, one_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  by_cases h : i = 0 <;> simp [h]

lemma out_inl (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    ∑ a ∈ (Gp G beta).arcs.filter (fun a => (Gp G beta).tail a = Sum.inl i), splitFlow x y a =
      if i = 0 then 0 else y i := by
  rw [Finset.sum_filter, sum_arcs]
  simp only [Gp, splitFlow, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add,
    Sum.inl.injEq]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  by_cases h : i = 0 <;> simp [h]

lemma in_inl (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    ∑ a ∈ (Gp G beta).arcs.filter (fun a => (Gp G beta).head a = Sum.inl i),
      (Gp G beta).mu a * splitFlow x y a = beta * inflow G x i := by
  rw [Finset.sum_filter, sum_arcs, inflow, Finset.sum_filter, Finset.mul_sum]
  simp only [Gp, splitFlow, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero,
    Sum.inl.injEq]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

end HCGnfAux

open HCGnfAux in
theorem solution {n : ℕ} [NeZero n] (G : Digraph n)
    (beta : ℝ) (hpos : 0 < beta) (hlt : beta < 1)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) :
    WH G beta x y ↔ (Gp G beta).IsFlow (splitFlow x y) := by
  have memI : ∀ e, (Sum.inl e : GpArc n) ∈ (Gp G beta).arcs ↔ e ∈ G.E := by
    intro e
    show Sum.inl e ∈ G.E.image Sum.inl ∪ (Finset.univ.erase (0 : Fin n)).image Sum.inr ↔ _
    simp
  have memR : ∀ j, (Sum.inr j : GpArc n) ∈ (Gp G beta).arcs ↔ j ≠ 0 := by
    intro j
    show Sum.inr j ∈ G.E.image Sum.inl ∪ (Finset.univ.erase (0 : Fin n)).image Sum.inr ↔ _
    simp
  constructor
  · rintro ⟨⟨hx0, hy0, h1, h2⟩, hxnn, hybd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rcases a with e | j
      · exact hx0 e (fun he => ha ((memI e).mpr he))
      · have : j = 0 := by by_contra hj; exact ha ((memR j).mpr hj)
        subst this; exact hy0
    · intro v
      rcases v with i | i
      · rw [out_inl, in_inl]
        have e1 := h1 i
        have e2 := h2 i
        show _ = (if i = 0 then -(beta ^ n) else -(beta ^ (n - 1)))
        by_cases hi : i = 0 <;> simp only [hi, if_true, if_false] at e1 e2 ⊢ <;> linarith
      · rw [out_inr, in_inr]
        exact h2 i
    · intro a ha
      rcases a with e | j
      · refine ⟨hxnn e ((memI e).mp ha), ?_⟩
        intro u hu; cases hu
      · have hj := (memR j).mp ha
        refine ⟨(hybd j hj).1, ?_⟩
        intro u hu
        simp only [Gp, Option.some.injEq] at hu
        subst hu
        exact (hybd j hj).2
  · rintro ⟨hz, hcons, hcap⟩
    have hx0 : ∀ e ∉ G.E, x e = 0 := fun e he => hz (Sum.inl e) (fun h => he ((memI e).mp h))
    have hy0 : y 0 = 0 := hz (Sum.inr 0) (fun h => (memR 0).mp h rfl)
    have h2 : ∀ i, outflow G x i - (if i = 0 then 0 else y i) =
        if i = 0 then 1 else beta ^ (n - 1) := by
      intro i
      have := hcons (Sum.inr i)
      rw [out_inr, in_inr] at this
      exact this
    have h3 : ∀ i, (if i = 0 then 0 else y i) - beta * inflow G x i =
        if i = 0 then -(beta ^ n) else -(beta ^ (n - 1)) := by
      intro i
      have := hcons (Sum.inl i)
      rw [out_inl, in_inl] at this
      exact this
    refine ⟨⟨hx0, hy0, ?_, h2⟩, ?_, ?_⟩
    · intro i
      have e2 := h2 i
      have e3 := h3 i
      by_cases hi : i = 0 <;> simp only [hi, if_true, if_false] at e2 e3 ⊢ <;> linarith
    · intro e he
      exact (hcap (Sum.inl e) ((memI e).mpr he)).1
    · intro i hi
      have := hcap (Sum.inr i) ((memR i).mpr hi)
      exact ⟨this.1, this.2 _ rfl⟩
