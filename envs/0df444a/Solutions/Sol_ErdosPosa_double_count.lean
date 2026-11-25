-- Prove2me | solution 1 for ErdosPosa.double_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:30.491043+00:00
-- url     : https://prove2.me/submissions/31e74ae7-2683-45a5-96b1-64f26e532ab5

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_ncard_eq_sum_ite
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}
open Classical
namespace ErdosPosa
theorem _root_.solution [Fintype V] :
    ∑ v, (if v ∉ T then ((H₀.neighborSet v ∩ T).ncard : ℤ) else 0) =
      ∑ t, (if t ∈ T then ((H₀.neighborSet t \ T).ncard : ℤ) else 0) := by
  classical
  have h1 : ∀ v, ((H₀.neighborSet v ∩ T).ncard : ℤ) =
      ∑ t, (if H₀.Adj v t ∧ t ∈ T then (1 : ℤ) else 0) := by
    intro v
    have : H₀.neighborSet v ∩ T = {t | H₀.Adj v t ∧ t ∈ T} := rfl
    rw [this, ncard_eq_sum_ite]; push_cast; rfl
  have h2 : ∀ t, ((H₀.neighborSet t \ T).ncard : ℤ) =
      ∑ v, (if H₀.Adj t v ∧ v ∉ T then (1 : ℤ) else 0) := by
    intro t
    have : H₀.neighborSet t \ T = {v | H₀.Adj t v ∧ v ∉ T} := rfl
    rw [this, ncard_eq_sum_ite]; push_cast; rfl
  simp only [h1, h2]
  have e1 : ∀ v, (if v ∉ T then ∑ t, (if H₀.Adj v t ∧ t ∈ T then (1 : ℤ) else 0) else 0) =
      ∑ t, (if v ∉ T ∧ t ∈ T ∧ H₀.Adj v t then (1 : ℤ) else 0) := by
    intro v
    by_cases hv : v ∈ T
    · simp [hv]
    · simp only [hv, not_false_eq_true, ↓reduceIte, true_and]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [and_comm]
  have e2 : ∀ t, (if t ∈ T then ∑ v, (if H₀.Adj t v ∧ v ∉ T then (1 : ℤ) else 0) else 0) =
      ∑ v, (if v ∉ T ∧ t ∈ T ∧ H₀.Adj v t then (1 : ℤ) else 0) := by
    intro t
    by_cases ht : t ∈ T
    · simp only [ht, ↓reduceIte, true_and]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [H₀.adj_comm]
      simp only [and_comm]
    · simp [ht]
  simp only [e1, e2]
  exact Finset.sum_comm
end ErdosPosa
