-- Prove2me | solution 2 for FairChores.SEFX_of_SEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:53:03.501015+00:00
-- url     : https://prove2.me/submissions/46fa6a5a-0f0f-4b8c-ae6d-76d2bb6c2b4e

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
theorem _root_.solution (h : SEFXlit c p o) : SEFX c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => Or.inr fun t ht => ?_⟩
  have hlit := (h i j).2 hi t ht
  have hct : cbar (c i) p t ≤ c i t := cbar_le_cost t
  rw [hi]
  linarith
end FairChores
