-- Prove2me | solution 1 for ErdosGirth.sum_wt_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:10.624593+00:00
-- url     : https://prove2.me/submissions/b6687778-71bd-4076-9bbc-25f2699b9026

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (p : ℝ) {B : Finset (Sym2 (Fin m))} (hB : B ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if Disjoint B S then wt m p S else 0) = (1 - p) ^ B.card := by
  have := Finset.prod_add (fun e => if e ∈ B then 0 else p) (fun _ => 1 - p) (pairs m)
  have h1 : ∏ i ∈ pairs m, ((if i ∈ B then 0 else p) + (1 - p)) = (1 - p) ^ B.card := by
    have : ∀ i, ((if i ∈ B then (0:ℝ) else p) + (1 - p)) = if i ∈ B then 1 - p else 1 := by
      intro i; split_ifs <;> ring
    simp only [this]
    rw [prod_ite_mem, inter_eq_right.mpr hB, prod_const]
  rw [h1] at this
  rw [this]
  refine sum_congr rfl fun S hS => ?_
  split_ifs with h
  · unfold wt; congr 1
    refine prod_congr rfl fun e he => ?_
    have : e ∉ B := fun heB => disjoint_left.mp h heB he
    simp [this]
  · obtain ⟨e, heB, heS⟩ := not_disjoint_iff.mp h
    rw [prod_eq_zero (i := e) heS (by simp [heB]), zero_mul]
end ErdosGirth
