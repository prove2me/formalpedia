-- Prove2me | solution 1 for FairChores.bag_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:38.308483+00:00
-- url     : https://prove2.me/submissions/4cb2a751-178b-46e1-83ed-cc7c5969abc5

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
import Theorems.Thm_FairChores_cbarSum_insert
import Theorems.Thm_FairChores_bag_exit
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbar_nonneg
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
variable {c p mu}
omit [Fintype T]
namespace FairChores
theorem _root_.solution (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    (A : Finset (Fin n)) (R : Finset T) :
    ∀ (m : ℕ) (X Psi : Finset T), X ⊆ R → Psi ⊆ R → Disjoint X Psi →
      (R \ (X ∪ Psi)).card ≤ m →
      (∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t) →
      (X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t) →
      (∃ j ∈ A, cbarSum (c j) p X < mu j) →
      BagGoal c p mu A R := by
  classical
  intro m
  induction m with
  | zero =>
    intro X Psi hX hPsi hdisj hcard hP hQ hU
    exact bag_exit hmu hX hPsi hdisj (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)) hP hQ hU
  | succ m ih =>
    intro X Psi hX hPsi hdisj hcard hP hQ hU
    rcases Finset.eq_empty_or_nonempty (R \ (X ∪ Psi)) with hAv | ⟨t, htAv⟩
    · exact bag_exit hmu hX hPsi hdisj hAv hP hQ hU
    obtain ⟨htR, htXPsi⟩ := Finset.mem_sdiff.mp htAv
    have htX : t ∉ X := fun h => htXPsi (Finset.mem_union_left _ h)
    have htPsi : t ∉ Psi := fun h => htXPsi (Finset.mem_union_right _ h)
    have hcardX : (R \ (insert t X ∪ Psi)).card ≤ m := by
      have hEq : R \ (insert t X ∪ Psi) = (R \ (X ∪ Psi)).erase t := by
        ext s
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hEq, Finset.card_erase_of_mem htAv]
      omega
    have hcardPsi : (R \ (X ∪ insert t Psi)).card ≤ m := by
      have hEq : R \ (X ∪ insert t Psi) = (R \ (X ∪ Psi)).erase t := by
        ext s
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hEq, Finset.card_erase_of_mem htAv]
      omega
    by_cases hall : ∀ j ∈ A, mu j ≤ cbarSum (c j) p (insert t X)
    · by_cases hsome : ∃ i ∈ A, cbarSum (c i) p (insert t X) ≤ 2 * mu i
      · -- the bag can be given away: the normal bag-filling case
        obtain ⟨i, hiA, hi⟩ := hsome
        exact Or.inr ⟨insert t X, Finset.insert_subset htR hX, ⟨t, Finset.mem_insert_self _ _⟩,
          i, hiA, hi, fun j hjA _ => Or.inl (hall j hjA)⟩
      · -- the chore `t` is put aside
        push_neg at hsome
        refine ih X (insert t Psi) hX (Finset.insert_subset htR hPsi) ?_ hcardPsi ?_ ?_ hU
        · exact Finset.disjoint_insert_right.mpr ⟨htX, hdisj⟩
        · intro j hjA
          by_cases hsat : mu j ≤ cbarSum (c j) p X
          · exact Or.inl hsat
          · push_neg at hsat
            have hPsi' : ∀ s ∈ Psi, mu j < cbar (c j) p s := by
              rcases hP j hjA with h | h
              · exact absurd h (not_le.mpr hsat)
              · exact h
            refine Or.inr fun s hs => ?_
            rcases Finset.mem_insert.mp hs with rfl | hsPsi
            · have h2 := hsome j hjA
              rw [cbarSum_insert htX] at h2
              linarith
            · exact hPsi' s hsPsi
        · intro hXe s hs j hjA
          rcases Finset.mem_insert.mp hs with rfl | hsPsi
          · have h2 := hsome j hjA
            rw [cbarSum_insert htX, hXe] at h2
            simpa [cbarSum] using h2
          · exact hQ hXe s hsPsi j hjA
    · -- some agent is still unsatisfied: keep filling the bag
      push_neg at hall
      obtain ⟨j1, hj1A, hj1⟩ := hall
      refine ih (insert t X) Psi (Finset.insert_subset htR hX) hPsi ?_ hcardX ?_ ?_
        ⟨j1, hj1A, hj1⟩
      · exact Finset.disjoint_insert_left.mpr ⟨htPsi, hdisj⟩
      · intro j hjA
        rcases hP j hjA with h | h
        · refine Or.inl (le_trans h ?_)
          rw [cbarSum_insert htX]
          have := cbar_nonneg (hc j) hp t
          linarith
        · exact Or.inr h
      · intro hXe
        exact absurd hXe (by simp)
end FairChores
