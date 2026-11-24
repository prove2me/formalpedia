-- Prove2me | solution 2 for FairChores.SEF1_of_SEF1lit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:06.437818+00:00
-- url     : https://prove2.me/submissions/cc619be8-e005-4885-a283-1d9390f332f6

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_cbar_le_cost


set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (h : SEF1lit c p o) : SEF1 c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => Or.inr ?_⟩
  obtain ⟨t, ht, hlit⟩ := (h i j).2 hi
  have hct : cbar (c i) p t ≤ c i t := cbar_le_cost t
  exact ⟨t, ht, by rw [hi]; linarith⟩
end FairChores
