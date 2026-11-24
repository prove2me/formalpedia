-- Prove2me | solution 1 for FairChores.SEF1_of_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:36:11.743642+00:00
-- url     : https://prove2.me/submissions/e72adc8f-86ea-49fc-a21c-52ca9ab4b392

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}


theorem solution (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t)
    (hvalid : o.Valid p) (h : SEFX c p o) : SEF1 c p o := by
  intro i j; obtain ⟨hi,hz⟩ := h i j; refine ⟨hi,?_⟩; intro hp0
  rcases hz hp0 with H | H
  · exact Or.inl H
  · by_cases he : (o.kept i).Nonempty
    · obtain ⟨t,ht⟩ := he; exact Or.inr ⟨t,ht,H t ht⟩
    · left; rw [Finset.not_nonempty_iff_eq_empty.mp he, hp0]; simp only [cbarSum, Finset.sum_empty, zero_add]
      exact add_nonneg (Finset.sum_nonneg (fun t _ => le_min (hc i t) (hp t))) (hvalid.2.2.2.1 j)
