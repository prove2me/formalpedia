-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.feigeNorkinChores_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:09.818923+00:00
-- url     : https://prove2.me/submissions/f72ba282-f48e-4378-b000-5efc5b90cbd6

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
import Theorems.Thm_FairChores_FeigeNorkinChores_feigeNorkinChores_core

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution (A : Fin 3 → Finset (Fin 8))
    (hcov : ∀ j : Fin 8, j ∈ A 0 ∨ j ∈ A 1 ∨ j ∈ A 2) :
    ∃ i : Fin 3, 380 ≤ ∑ j ∈ A i, fcW i j := by
  classical
  set f : Fin 8 → Fin 3 := fun j => if j ∈ A 0 then 0 else if j ∈ A 1 then 1 else 2 with hf
  have hsub : ∀ i, Finset.univ.filter (fun j => f j = i) ⊆ A i := by
    intro i j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases h0 : j ∈ A 0
    · have : f j = 0 := by simp [hf, h0]
      rw [this] at hj; rw [← hj]; exact h0
    · by_cases h1 : j ∈ A 1
      · have : f j = 1 := by simp [hf, h0, h1]
        rw [this] at hj; rw [← hj]; exact h1
      · have h2 : j ∈ A 2 := by rcases hcov j with h | h | h <;> tauto
        have : f j = 2 := by simp [hf, h0, h1]
        rw [this] at hj; rw [← hj]; exact h2
  obtain ⟨i, hi⟩ := feigeNorkinChores_core f
  refine ⟨i, le_trans hi ?_⟩
  have hrw : (∑ j, if f j = i then fcW i j else 0)
      = ∑ j ∈ Finset.univ.filter (fun j => f j = i), fcW i j := by
    rw [Finset.sum_filter]
  rw [hrw]
  exact Finset.sum_le_sum_of_subset (hsub i)
end FairChores.FeigeNorkinChores
