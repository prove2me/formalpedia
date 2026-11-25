-- Prove2me | solution 1 for ErdosGirth.sum_wt_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:06.205204+00:00
-- url     : https://prove2.me/submissions/a18fcefc-9111-4a35-9a24-3be20a13866d

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (p : ℝ) {A : Finset (Sym2 (Fin m))} (hA : A ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if A ⊆ S then wt m p S else 0) = p ^ A.card := by
  have := Finset.prod_add (fun _ => p) (fun e => if e ∈ A then 0 else 1 - p) (pairs m)
  have h1 : ∏ i ∈ pairs m, (p + if i ∈ A then 0 else 1 - p) = p ^ A.card := by
    have : ∀ i, (p + if i ∈ A then (0:ℝ) else 1 - p) = if i ∈ A then p else 1 := by
      intro i; split_ifs <;> ring
    simp only [this]
    rw [prod_ite_mem, inter_eq_right.mpr hA, prod_const]
  rw [h1] at this
  rw [this]
  refine sum_congr rfl fun S hS => ?_
  split_ifs with h
  · unfold wt; congr 1
    refine prod_congr rfl fun e he => ?_
    have : e ∉ A := fun heA => (mem_sdiff.mp he).2 (h heA)
    simp [this]
  · obtain ⟨e, heA, heS⟩ := not_subset.mp h
    rw [prod_eq_zero (i := e) (mem_sdiff.mpr ⟨hA heA, heS⟩) (by simp [heA]), mul_zero]
end ErdosGirth
