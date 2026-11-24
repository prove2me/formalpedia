-- Prove2me | solution 1 for FairSelling.FeigeNorkin.feigeNorkin_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:55.057895+00:00
-- url     : https://prove2.me/submissions/ba7875d3-28e9-47e9-a024-59b1dfe4e6dd

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
import Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_core

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    ∃ i : Fin 3, (∑ j ∈ A i, fnW i j) ≤ 33 := by
  classical
  set f : Fin 8 → Fin 3 := fun j => if j ∈ A 1 then 1 else if j ∈ A 2 then 2 else 0 with hf
  have hsub : ∀ i, A i ⊆ Finset.univ.filter (fun j => f j = i) := by
    intro i j hj
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi3 with rfl | rfl | rfl
    · have h1 : j ∉ A 1 := Finset.disjoint_left.1 (hA 0 1 (by decide)) hj
      have h2 : j ∉ A 2 := Finset.disjoint_left.1 (hA 0 2 (by decide)) hj
      simp [hf, h1, h2]
    · simp [hf, hj]
    · have h1 : j ∉ A 1 := Finset.disjoint_left.1 (hA 2 1 (by decide)) hj
      simp [hf, h1, hj]
  obtain ⟨i, hi⟩ := feigeNorkin_core f
  refine ⟨i, le_trans ?_ hi⟩
  have : (∑ j, if f j = i then fnW i j else 0)
      = ∑ j ∈ Finset.univ.filter (fun j => f j = i), fnW i j := by
    rw [Finset.sum_filter]
  rw [this]
  exact Finset.sum_le_sum_of_subset (hsub i)
end FairSelling.FeigeNorkin
